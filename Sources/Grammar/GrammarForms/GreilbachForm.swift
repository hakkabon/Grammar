//
//  GreilbachForm.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2024/01/04.
//  Copyright © 2024 hakkabon software. All rights reserved.
//
//  Converts a context-free grammar to Greibach Normal Form (GNF).
//
//  A grammar is in GNF when every production has the shape:
//    • A → a α        (starts with exactly one terminal, followed by zero or more non-terminals)
//
//  The conversion follows these steps:
//    1. Eliminate ε-productions  (reused from CNF converter)
//    2. Eliminate unit productions  (reused from CNF converter)
//    3. Order non-terminals A1 … An and substitute so that Ai → Aj γ only when j > i
//       (this eliminates indirect left recursion)
//    4. Eliminate immediate left recursion for each Ai
//    5. Back-substitute from An down to A1 so every rule starts with a terminal
//

import Foundation

extension Grammar {

    // MARK: - Public entry point

    /// Returns a new grammar whose productions are in Greibach Normal Form.
    public func toGreibachNormalForm() -> Grammar {
        let converter = GreibachNormalFormConverter()
        let gnfProductions = converter.convert(productions, startSymbol: start)
        return Grammar(
            productions: gnfProductions,
            start: start,
            empty: epsilon,
            lexicalTokens: lexicalTokens,
            generatedNonTerminals: generatedNonTerminals
        )
    }

    // MARK: - Converter

    class GreibachNormalFormConverter {

        private var counter = 0

        private func freshNT(prefix: String) -> NonTerminal {
            defer { counter += 1 }
            return NonTerminal(name: "\(prefix)\(counter)")
        }

        // MARK: Convert

        /// Convert the given productions to GNF.
        func convert(_ productions: [Production], startSymbol: NonTerminal) -> [Production] {
            counter = 0

            let cnf = ChomskyNormalFormConverter()

            var grouped = group(productions)

            // Step 1 – remove ε-productions
            grouped = cnf.eliminateEpsilonProductions(grouped)

            // Step 2 – remove unit productions
            grouped = cnf.eliminateUnitProductions(grouped)

            // Step 3 & 4 – order NTs, substitute to remove left recursion
            grouped = eliminateLeftRecursion(grouped)

            // Step 5 – back-substitute so every rule starts with a terminal
            grouped = backSubstitute(grouped)

            // Step 6 – replace terminals in the tail (positions ≥ 1) with fresh NTs
            grouped = wrapTailTerminals(grouped)

            return ungroup(grouped)
        }

        // MARK: - Step 3 & 4: Eliminate left recursion (Rosenkrantz–Stearns algorithm)

        /// Orders non-terminals A1 … An, then for each Ai:
        ///   • Replaces Ai → Aj γ (j < i) by substituting all Aj-rules
        ///   • Eliminates any resulting immediate left recursion via a fresh NT Ai'
        private func eliminateLeftRecursion(
            _ grammar: [NonTerminal: [[Symbol]]]
        ) -> [NonTerminal: [[Symbol]]] {

            // Stable ordering so the algorithm is deterministic
            let order = grammar.keys.sorted { $0.name < $1.name }
            var result = grammar

            for i in 0..<order.count {
                let ai = order[i]
                guard let aiRules = result[ai] else { continue }

                // Substitute Ai → Aj γ where j < i
                var expanded: [[Symbol]] = []
                for rule in aiRules {
                    if let firstNT = rule.first?.nonTerminal,
                       let j = order.firstIndex(of: firstNT), j < i,
                       let ajRules = result[firstNT] {
                        // Replace with all Aj-productions prepended to the tail
                        let tail = Array(rule.dropFirst())
                        for ajRule in ajRules {
                            expanded.append(ajRule + tail)
                        }
                    } else {
                        expanded.append(rule)
                    }
                }
                result[ai] = expanded

                // Eliminate immediate left recursion for Ai
                result = eliminateImmediateLeftRecursion(result, for: ai)
            }
            return result
        }

        /// Rewrites immediate left recursion  A → A α | β  into
        ///   A  → β A'  (for each non-recursive β)
        ///   A' → α A'  (for each recursive α)
        ///   A' → ε     (base case)
        private func eliminateImmediateLeftRecursion(
            _ grammar: [NonTerminal: [[Symbol]]],
            for nt: NonTerminal
        ) -> [NonTerminal: [[Symbol]]] {

            guard let rules = grammar[nt] else { return grammar }

            var recursive: [[Symbol]] = []     // α  in  A → A α
            var nonRecursive: [[Symbol]] = []  // β  in  A → β

            for rule in rules {
                if rule.first?.nonTerminal == nt {
                    recursive.append(Array(rule.dropFirst()))
                } else {
                    nonRecursive.append(rule)
                }
            }

            guard !recursive.isEmpty else { return grammar }

            var result = grammar
            let prime = freshNT(prefix: "\(nt.name)'")

            // A  → β A'
            result[nt] = nonRecursive.map { $0 + [.nonTerminal(prime)] }

            // A' → α A' | ε
            // The epsilon alternative is the canonical empty rule `[]`; intermediate
            // raw-[Symbol] rules in this converter are re-wrapped as `Production`
            // values by `ungroup(_:)`, which would normalize this away regardless,
            // but writing `[]` here keeps every stage of the pipeline consistent.
            var primeRules: [[Symbol]] = recursive.map { $0 + [.nonTerminal(prime)] }
            primeRules.append([])
            result[prime] = primeRules

            return result
        }

        // MARK: - Step 5: Back-substitution to ensure terminal-first

        /// Works from the last non-terminal back to the first, substituting
        /// any rule that starts with a non-terminal until every rule starts
        /// with a terminal (or epsilon).
        private func backSubstitute(
            _ grammar: [NonTerminal: [[Symbol]]]
        ) -> [NonTerminal: [[Symbol]]] {

            let order = grammar.keys.sorted { $0.name < $1.name }
            var result = grammar

            // Iterate in reverse order for back-substitution
            for i in stride(from: order.count - 1, through: 0, by: -1) {
                let ai = order[i]
                guard let aiRules = result[ai] else { continue }

                var newRules: [[Symbol]] = []
                for rule in aiRules {
                    let expanded = expandUntilTerminalFirst(
                        rule: rule,
                        grammar: result,
                        depth: 0,
                        maxDepth: 200
                    )
                    newRules.append(contentsOf: expanded.isEmpty ? [rule] : expanded)
                }
                // Deduplicate
                var seen: [[Symbol]] = []
                for r in newRules where !seen.contains(r) { seen.append(r) }
                result[ai] = seen
            }
            return result
        }

        /// Recursively expands a rule until its first symbol is a terminal.
        /// Returns the set of fully-expanded rules, or an empty array if the
        /// rule already starts with a terminal / epsilon.
        private func expandUntilTerminalFirst(
            rule: [Symbol],
            grammar: [NonTerminal: [[Symbol]]],
            depth: Int,
            maxDepth: Int
        ) -> [[Symbol]] {

            guard !rule.isEmpty else { return [[]] }

            let head = rule[0]
            let tail = Array(rule.dropFirst())

            // Already starts with a terminal or epsilon — nothing to do
            if head.isTerminal || head.isEpsilon { return [rule] }

            guard depth < maxDepth,
                  let firstNT = head.nonTerminal,
                  let ntRules = grammar[firstNT] else { return [rule] }

            var result: [[Symbol]] = []
            for ntRule in ntRules {
                let combined = ntRule + tail
                let further = expandUntilTerminalFirst(
                    rule: combined,
                    grammar: grammar,
                    depth: depth + 1,
                    maxDepth: maxDepth
                )
                result.append(contentsOf: further.isEmpty ? [combined] : further)
            }
            return result
        }

        // MARK: - Step 6: Wrap tail terminals

        /// GNF requires that every symbol after the leading terminal is a non-terminal.
        /// This step replaces any terminal `a` appearing at position ≥ 1 in a rule with
        /// a fresh non-terminal `Ta` that has the single production `Ta → a`.
        private func wrapTailTerminals(
            _ grammar: [NonTerminal: [[Symbol]]]
        ) -> [NonTerminal: [[Symbol]]] {

            var result = grammar
            var termMap: [String: NonTerminal] = [:]

            for (nt, rules) in grammar {
                var newRules: [[Symbol]] = []
                for rule in rules {
                    guard rule.count >= 2 else {
                        newRules.append(rule)
                        continue
                    }
                    // Keep the first symbol as-is (it must already be a terminal after step 5)
                    let head = rule[0]
                    let tail: [Symbol] = rule.dropFirst().map { sym in
                        guard sym.isTerminal else { return sym }
                        let key = sym.description
                        if let existing = termMap[key] { return .nonTerminal(existing) }
                        let fresh = freshNT(prefix: "T")
                        termMap[key] = fresh
                        result[fresh] = [[sym]]
                        return .nonTerminal(fresh)
                    }
                    newRules.append([head] + tail)
                }
                result[nt] = newRules
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
