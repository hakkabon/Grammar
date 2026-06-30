//
//  ChomskyForm.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/07.
//  Copyright © 2023 hakkabon software. All rights reserved.
//
//  Converts a context-free grammar to Chomsky Normal Form (CNF).
//
//  A grammar is in CNF when every production has one of these shapes:
//    • A → a          (single terminal)
//    • A → B C        (exactly two non-terminals)
//    • S → ε          (only the start symbol may derive epsilon)
//
//  The conversion follows four classical steps:
//    1. Eliminate ε-productions (nullable non-terminals)
//    2. Eliminate unit productions  (A → B)
//    3. Replace terminals in long rules with fresh non-terminals  (TERM step)
//    4. Break rules longer than two symbols into binary pairs     (BIN step)
//

import Foundation

extension Grammar {

    // MARK: - Public entry point

    /// Returns a new grammar whose productions are in Chomsky Normal Form.
    public func toChomskyNormalForm() -> Grammar {
        let converter = ChomskyNormalFormConverter()
        let cnfProductions = converter.convert(productions, startSymbol: start)
        return Grammar(
            productions: cnfProductions,
            start: start,
            empty: epsilon,
            lexicalTokens: lexicalTokens,
            generatedNonTerminals: generatedNonTerminals
        )
    }

    // MARK: - Converter

    class ChomskyNormalFormConverter {

        /// Unique-name counter; reset before each conversion.
        private var counter = 0

        private func freshNT(prefix: String) -> NonTerminal {
            defer { counter += 1 }
            return NonTerminal(name: "\(prefix)\(counter)")
        }

        // MARK: Convert

        /// Convert the given productions to CNF.
        /// - Parameters:
        ///   - productions: The input productions.
        ///   - startSymbol: The grammar's start symbol (needed to preserve S → ε if required).
        /// - Returns: Productions in Chomsky Normal Form.
        func convert(_ productions: [Production], startSymbol: NonTerminal) -> [Production] {
            counter = 0

            var grouped = group(productions)

            // Step 1 – remove ε-productions
            grouped = eliminateEpsilonProductions(grouped)

            // Step 2 – remove unit productions (A → B)
            grouped = eliminateUnitProductions(grouped)

            // Step 3 – TERM: replace terminals in rules of length ≥ 2
            grouped = termStep(grouped)

            // Step 4 – BIN: binarise rules of length ≥ 3
            grouped = binStep(grouped)

            return ungroup(grouped)
        }

        // MARK: - Step 1: Eliminate ε-productions

        /// Finds all nullable non-terminals and rewrites every production by
        /// generating all subsets that omit nullable symbols, then drops the
        /// original ε-productions.
        func eliminateEpsilonProductions(
            _ grammar: [NonTerminal: [[Symbol]]]
        ) -> [NonTerminal: [[Symbol]]] {

            // --- compute nullable set ---
            var nullable = Set<NonTerminal>()
            var changed = true
            while changed {
                changed = false
                for (nt, rules) in grammar where !nullable.contains(nt) {
                    for rule in rules {
                        let ruleIsNullable = rule.isEmpty || rule.allSatisfy {
                            $0.isEpsilon || ($0.nonTerminal.map { nullable.contains($0) } ?? false)
                        }
                        if ruleIsNullable {
                            nullable.insert(nt)
                            changed = true
                            break
                        }
                    }
                }
            }

            // --- rewrite productions ---
            var result: [NonTerminal: [[Symbol]]] = [:]
            for (nt, rules) in grammar {
                var newRules: [[Symbol]] = []
                for rule in rules {
                    // Drop pure ε-productions. `rule` originates from `Production.rule`
                    // (see `group(_:)` below), which is normalized at creation to `[]`
                    // for any epsilon production, so `rule.isEmpty` is the case that
                    // actually fires; the single-symbol check is kept only as a
                    // defensive fallback for raw `[Symbol]` rules built up elsewhere
                    // in this converter that haven't yet round-tripped through `Production`.
                    if rule.count == 1 && rule[0].isEpsilon { continue }
                    if rule.isEmpty { continue }

                    // Generate all non-empty subsets by omitting nullable positions
                    for combo in nullableCombinations(rule: rule, nullable: nullable)
                    where !combo.isEmpty {
                        if !newRules.contains(combo) { newRules.append(combo) }
                    }
                }
                result[nt] = newRules
            }
            return result
        }

        /// Recursively generates all combinations of `rule` where nullable symbols
        /// may be present or absent.
        private func nullableCombinations(
            rule: [Symbol],
            nullable: Set<NonTerminal>
        ) -> [[Symbol]] {
            guard !rule.isEmpty else { return [[]] }

            let head = rule[0]
            let tail = Array(rule.dropFirst())
            let tailCombos = nullableCombinations(rule: tail, nullable: nullable)

            var result: [[Symbol]] = []
            // Always include head
            for combo in tailCombos { result.append([head] + combo) }
            // Optionally omit head if it is nullable
            if head.nonTerminal.map({ nullable.contains($0) }) ?? false {
                result.append(contentsOf: tailCombos)
            }
            return result
        }

        // MARK: - Step 2: Eliminate unit productions

        /// Removes all unit productions A → B by computing the transitive closure
        /// of the unit-production relation and substituting the non-unit rules.
        func eliminateUnitProductions(
            _ grammar: [NonTerminal: [[Symbol]]]
        ) -> [NonTerminal: [[Symbol]]] {

            // Build unit-reachability: unitReach[A] = { B | A =>* B via unit steps }
            var unitReach: [NonTerminal: Set<NonTerminal>] = [:]
            for nt in grammar.keys { unitReach[nt] = [nt] }

            var changed = true
            while changed {
                changed = false
                for (nt, rules) in grammar {
                    for rule in rules where rule.count == 1 {
                        guard let target = rule[0].nonTerminal else { continue }
                        let reachableViaTarget = unitReach[target] ?? [target]
                        for reached in reachableViaTarget {
                            if unitReach[nt]?.insert(reached).inserted == true {
                                changed = true
                            }
                        }
                    }
                }
            }

            // Build new grammar: for each A, collect all non-unit rules reachable from A
            var result: [NonTerminal: [[Symbol]]] = [:]
            for nt in grammar.keys {
                var newRules: [[Symbol]] = []
                for reachable in unitReach[nt] ?? [] {
                    for rule in grammar[reachable] ?? [] {
                        // Skip unit productions
                        if rule.count == 1 && rule[0].isNonTerminal { continue }
                        if !newRules.contains(rule) { newRules.append(rule) }
                    }
                }
                result[nt] = newRules
            }
            return result
        }

        // MARK: - Step 3: TERM – replace terminals in long rules

        /// For every rule of length ≥ 2, replaces each terminal `a` with a fresh
        /// non-terminal `Ta` that has the single production `Ta → a`.
        private func termStep(
            _ grammar: [NonTerminal: [[Symbol]]]
        ) -> [NonTerminal: [[Symbol]]] {

            var result = grammar
            // Map from terminal description → fresh NT
            var termMap: [String: NonTerminal] = [:]

            for (nt, rules) in grammar {
                var newRules: [[Symbol]] = []
                for rule in rules {
                    if rule.count < 2 {
                        newRules.append(rule)
                        continue
                    }
                    let rewritten: [Symbol] = rule.map { sym in
                        guard sym.isTerminal else { return sym }
                        let key = sym.description
                        if let existing = termMap[key] { return .nonTerminal(existing) }
                        let fresh = freshNT(prefix: "T")
                        termMap[key] = fresh
                        result[fresh] = [[sym]]
                        return .nonTerminal(fresh)
                    }
                    newRules.append(rewritten)
                }
                result[nt] = newRules
            }
            return result
        }

        // MARK: - Step 4: BIN – binarise long rules

        /// Breaks every rule of length ≥ 3 into a right-branching chain of binary rules.
        ///
        /// Example:  A → B C D E
        ///   becomes A → B Y0
        ///           Y0 → C Y1
        ///           Y1 → D E
        private func binStep(
            _ grammar: [NonTerminal: [[Symbol]]]
        ) -> [NonTerminal: [[Symbol]]] {

            var result: [NonTerminal: [[Symbol]]] = [:]

            for (nt, rules) in grammar {
                var newRules: [[Symbol]] = []
                for rule in rules {
                    if rule.count <= 2 {
                        newRules.append(rule)
                        continue
                    }
                    // Build right-branching chain
                    // rule = [s0, s1, s2, ..., sN]
                    // We want: nt → s0 Y0, Y0 → s1 Y1, ..., Y(N-2) → s(N-1) sN
                    var chain = rule
                    var currentNT = nt
                    var firstRule = true

                    while chain.count > 2 {
                        let head = chain[0]
                        let fresh = freshNT(prefix: "Y")
                        let binaryRule: [Symbol] = [head, .nonTerminal(fresh)]

                        if firstRule {
                            newRules.append(binaryRule)
                            firstRule = false
                        } else {
                            if result[currentNT] == nil { result[currentNT] = [] }
                            result[currentNT]?.append(binaryRule)
                        }
                        currentNT = fresh
                        chain = Array(chain.dropFirst())
                    }
                    // Last two symbols
                    if result[currentNT] == nil { result[currentNT] = [] }
                    result[currentNT]?.append(chain)
                }
                if result[nt] == nil { result[nt] = [] }
                result[nt]?.append(contentsOf: newRules)
            }
            return result
        }

        // MARK: - Helpers

        private func group(_ productions: [Production]) -> [NonTerminal: [[Symbol]]] {
            var grouped: [NonTerminal: [[Symbol]]] = [:]
            for prod in productions {
                grouped[prod.goal, default: []].append(prod.rule)
            }
            return grouped
        }

        private func ungroup(_ grouped: [NonTerminal: [[Symbol]]]) -> [Production] {
            grouped.flatMap { nt, rules in rules.map { Production(goal: nt, rule: $0) } }
        }
    }
}
