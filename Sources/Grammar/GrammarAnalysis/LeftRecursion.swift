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
        
        // Create a mutable copy of productions grouped by their goal.
        // We will update this in-place during the algorithm.
        var currentProductions = Dictionary(grouping: Array(self.productions), by: \.goal)
        
        // Create an ordered list of the original non-terminals.
        let originalNonTerminals = nonTerminals.sorted { $0 < $1 }
        
        // Track all non-terminals to avoid name collisions.
        var allNTs = self.nonTerminals

        for i in 0..<originalNonTerminals.count {
            let ai = originalNonTerminals[i]
            
            for j in 0..<i {
                let aj = originalNonTerminals[j]
                
                // Get the current rules for Ai.
                let rulesForAi = currentProductions[ai] ?? []
                var updatedRulesForAi: [Production] = []
                
                for prod in rulesForAi {
                    if prod.rule.first == .nonTerminal(aj) {
                        let tail = Array(prod.rule.dropFirst())
                        let rulesForAj = currentProductions[aj] ?? []
                        for prodJ in rulesForAj {
                            updatedRulesForAi.append(Production(goal: ai, rule: prodJ.rule + tail))
                        }
                    } else {
                        updatedRulesForAi.append(prod)
                    }
                }
                currentProductions[ai] = updatedRulesForAi
            }
            
            // Eliminate immediate left recursion for Ai.
            let rulesForAi = currentProductions[ai] ?? []
            let alphaRules = rulesForAi.filter { $0.rule.first == .nonTerminal(ai) }
            let betaRules = rulesForAi.filter { $0.rule.first != .nonTerminal(ai) }
            
            if !alphaRules.isEmpty {
                let prime = generateNonterminal(withPrefix: ai.name, nonTerminals: allNTs)
                allNTs.insert(prime)
                
                // Ai -> beta Ai'
                var newAiRules: [Production] = []
                for betaRule in betaRules {
                    newAiRules.append(Production(goal: ai, rule: betaRule.rule + [.nonTerminal(prime)]))
                }
                
                // Ai' -> alpha Ai' | epsilon
                var primeRules: [Production] = []
                for alphaRule in alphaRules {
                    let alpha = Array(alphaRule.rule.dropFirst())
                    primeRules.append(Production(goal: prime, rule: alpha + [.nonTerminal(prime)]))
                }
                // Add epsilon rule
                primeRules.append(Production(goal: prime, rule: []))
                
                currentProductions[ai] = newAiRules
                currentProductions[prime] = primeRules
            }
        }
        
        return currentProductions.values.flatMap { $0 }
    }
}
