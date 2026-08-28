//
//  LeftFactoring.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/09.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation

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
    public func leftFactoring(logging: GrammarLogging = .disabled) -> [Production] {
        var currentProductions = Set(self.productions)
        var nonTerminals = self.nonTerminals

        func suffix(from alpha: [Symbol], in rule: [Symbol]) -> [Symbol] {
            return Array(rule.suffix(from: alpha.endIndex))
        }

        func allRules(for nonTerminal: NonTerminal) -> [[Symbol]] {
            let prods = currentProductions.filter { $0.goal == nonTerminal }
            return prods.map { $0.rule }
        }

        func findCommonPrefix(in rules: [[Symbol]]) -> [Symbol]? {
            let nontermGroup = Dictionary(grouping: rules.filter { !$0.isEmpty }) { $0[0] }
            
            var bestPrefix: [Symbol]? = nil
            for (_, groupRules) in nontermGroup where groupRules.count > 1 {
                let firstRule = groupRules[0]
                let common = groupRules.dropFirst().reduce(firstRule) { $0.commonPrefix(with: $1) }
                if !common.isEmpty {
                    if bestPrefix == nil || common.count > bestPrefix!.count {
                        bestPrefix = common
                    }
                }
            }
            return bestPrefix
        }

        var changed = true
        while changed {
            changed = false
            
            // We need to iterate over a snapshot of nonTerminals since we might add new ones.
            let ntSnapshot = Array(nonTerminals).sorted { $0.name < $1.name }
            for nonTerminal in ntSnapshot {
                let rules = allRules(for: nonTerminal)
                if let alpha = findCommonPrefix(in: rules) {
                    let V = generateNonterminal(withPrefix: "V", nonTerminals: nonTerminals)
                    nonTerminals.insert(V)
                    
                    logging.information("non-terminal '\(nonTerminal)' longest common prefix: \(alpha)", category: .grammar)
                    
                    // Filter productions of `nonTerminal` that start with alpha
                    let prodsToFactor = currentProductions.filter { $0.goal == nonTerminal && $0.rule.hasPrefix(alpha) }
                    
                    // Remove the factored productions
                    for prod in prodsToFactor {
                        currentProductions.remove(prod)
                        
                        let sfx = suffix(from: alpha, in: prod.rule)
                        let newProd = Production(goal: V, rule: sfx)
                        currentProductions.insert(newProd)
                    }
                    
                    // Add the new factored production A -> alpha V
                    let parentProd = Production(goal: nonTerminal, rule: alpha + [Symbol.nonTerminal(V)])
                    currentProductions.insert(parentProd)
                    
                    changed = true
                    break // Break the inner loop to restart with updated productions and non-terminals
                }
            }
        }
        
        return Array(currentProductions)
    }
}
