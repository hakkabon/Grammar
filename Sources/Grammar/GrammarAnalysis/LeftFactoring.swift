//
//  LeftFactoring.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/09.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation
import OSLog

extension Grammar {

    enum Prefix {
        case prefix([Symbol])
        case empty
    }

    enum Suffix {
        case suffix([Symbol])
        case empty
    }

    /// Algorithm 4.21
    /// [2] Compilers: Principles, Techniques, and Tools
    ///     or
    /// 8.2.5.2 Left-Factoring
    /// [1] Parsing Techniques
    ///     or
    /// 5.5.1 Common Prefixes
    /// [3] Crafting a compiler
    ///
    /// procedure Factor( )
    /// foreach A ∈ N do
    ///     α ← LongestCommonPrefix(ProductionsFor(A))
    ///     while |α| > 0 do
    ///         V ← new NonTerminal()
    ///         Productions ← Productions ∪ { A → αV }
    ///         foreach p ∈ ProductionsFor(A) | RHS(p) = αβp do
    ///             Productions ← Productions − { p }
    ///             Productions ← Productions ∪ { V → βp }
    ///         α ← LongestCommonPrefix(ProductionsFor(A))
    /// end
    public func leftFactoring() -> [Production] {
        var currentProductions = Set(self.productions)
        var nonTerminals = self.nonTerminals

        func longestCommonPrefix(_ rule: [[Symbol]]) -> Prefix {
            guard let first = rule.first.map({ $0 }) else { return .empty }
            let prefix = rule.dropFirst().reduce(first, { $0.commonPrefix(with: $1) })
            return prefix == [] ? .empty : .prefix(prefix)
        }

        func suffix(from alpha: [Symbol], in rule: [Symbol]) -> Suffix {
            let beta = rule.suffix(from: alpha.endIndex)
            return beta == [] ? .empty : .suffix(Array(beta))
        }

        func allRules(for nonTerminal: NonTerminal) -> [[Symbol]] {
            let groupedProductions = Dictionary(grouping: Array(currentProductions), by: \.goal)
            if let prods: [Production] = groupedProductions[nonTerminal] {
                return prods.map { $0.rule }
            }
            return []
        }
        
        func productions(for nonTerminal: NonTerminal) -> [Production]? {
            let groupedProductions = Dictionary(grouping: Array(currentProductions), by: \.goal)
            return groupedProductions[nonTerminal]
        }

        for nonTerminal in nonTerminals {
            while case let .prefix(alpha) = longestCommonPrefix(allRules(for: nonTerminal)), allRules(for: nonTerminal).count > 1 {
                Logger.grammar.info("non-terminal '\(nonTerminal)' longest common prefix: \(alpha)")
                let V = generateNonterminal(withPrefix: "V", nonTerminals: nonTerminals)
                nonTerminals.insert(V)
                // Productions ∪ { A → αV }
                let p = Production(goal: nonTerminal, rule: alpha + [Symbol.nonTerminal(V)])
                currentProductions.insert(p)
                Logger.grammar.info("  add production: \(p)")

                if let prods = productions(for: nonTerminal) {
                    for prod in prods {
                        // all rules with prefix but except A → αV
                        if prod.rule.hasPrefix(alpha) && !prod.rule.contains(.nonTerminal(V)) {
                            // productions − { p }
                            currentProductions.remove(prod)
                            Logger.grammar.info("  remove production: \(prod)")
                            
                            // productions ∪ { V → βp }
                            let p2: Production
                            switch suffix(from: alpha, in: prod.rule) {
                            case .suffix(let beta):
                                p2 = Production(goal: V, rule: beta)
                            case .empty:
                                // The epsilon alternative is the canonical empty rule `[]`.
                                p2 = Production(goal: V, rule: [])
                            }

                            currentProductions.insert(p2)
                            Logger.grammar.info("  add production from suffix of truncated production: \(p2)")
                        }
                    }
                }
            }
        }
        return Array(currentProductions)
    }
}
