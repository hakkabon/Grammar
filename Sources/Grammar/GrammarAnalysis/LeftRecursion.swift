//
//  LeftRecursion.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/09.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation
import OSLog

/// Eliminating Left Recursion is described in detail in the following books:
/// [1] Parsing Techniques, 6.4 Eliminating Left Recursion
/// [2] Compilers: Principles, Techniques, and Tools, Algorithm 4.19
///
/// Wikipedia has a good explanation in English:
///     https://en.wikipedia.org/wiki/Left_recursion#Removing_left_recursion
extension Grammar {
    
    /// Removes all left recursion (direct and indirect) from the grammar.
    public func eliminateLeftRecursion() -> [Production] {
        
        let groupedProductions = Dictionary(grouping: Array(self.productions), by: \.goal)
        // Create an ordered list of non-terminals
        let nonTerminals = nonTerminals.sorted { $0 < $1 }
        var newProductions: [Production] = []

        /// Removes direct left recursion for a single non-terminal.
        func removeDirectLeftRecursion(for nonTerminal: NonTerminal) -> [Production] {
            guard let prods = groupedProductions[nonTerminal] else { return [] }
            var nonTerminals = self.nonTerminals
            
            // Partition productions into left-recursive and non-left-recursive
            let alphaProductions = prods.filter { $0.rule.first == Symbol.nonTerminal(nonTerminal) }
            let betaProductions = prods.filter { $0.rule.first != Symbol.nonTerminal(nonTerminal) }
            
            guard !alphaProductions.isEmpty else { return [] }
            
            // Create a new non-terminal
            let newNonTerminalName = generateNonterminal(withPrefix: nonTerminal.name, nonTerminals: nonTerminals)
            nonTerminals.insert(newNonTerminalName)
            let newNonTerminal = Symbol.nonTerminal(newNonTerminalName)
            
            // Rewrite original productions
            var newLhsProductions: [Production] = []
            for betaRule in betaProductions {
                // New rule: A -> beta A'
                newLhsProductions.append(Production(goal: nonTerminal, rule: betaRule.rule + [newNonTerminal]))
            }
            
            // Define productions for the new non-terminal
            var newRhsProductions: [Production] = []
            for alphaRule in alphaProductions {
                // New rule: A' -> alpha A'
                let alphaPart = Array(alphaRule.rule.dropFirst())
                newRhsProductions.append(Production(goal: newNonTerminalName, rule: alphaPart + [newNonTerminal]))
            }
            // Add epsilon production: A' -> ε, represented as the canonical empty rule `[]`.
            newRhsProductions.append(Production(goal: newNonTerminalName, rule: []))
            
            return newLhsProductions + newRhsProductions
        }
        
        for (i, nonTerminal_i) in nonTerminals.enumerated() {
            for j in 0..<i {
                let nonTerminal_j = Symbol.nonTerminal(nonTerminals[j])

                // Find and replace productions of the form Ai -> Aj*...
                var updatedProductionsFor_i: [Production] = []
                if let rules_i = groupedProductions[nonTerminal_i] {
                    for rule_i in rules_i {
                        if rule_i.rule.first == nonTerminal_j {
                            // Substitute Aj productions into Ai
                            if let rules_j = groupedProductions[nonTerminals[j]] {
                                for rule_j in rules_j {
                                    let newRhs = rule_j.rule + rule_i.rule.dropFirst()
                                    updatedProductionsFor_i.append(Production(goal: nonTerminal_i, rule: newRhs))
                                }
                            }
                        } else {
                            // Keep non-Aj-starting productions
                            updatedProductionsFor_i.append(rule_i)
                        }
                    }
                    newProductions += updatedProductionsFor_i
                }
            }
            // After all substitutions, remove any direct left recursion for nonTerminal_i
            newProductions += removeDirectLeftRecursion(for: nonTerminal_i)
        }
        return newProductions
    }
}
