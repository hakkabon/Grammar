//
//  Utils.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2026/01/02.
//

import Foundation

//TODO: THIS IS NOT NEEDED - HAS TO GO AWAY, pronto!

extension Grammar {
    
    class GrammarUtils {
        /// Counter for generating unique non-terminals
        private static var ntCounter = 0
        
        /// Generate a new unique non-terminal
        static func generateNonTerminal(prefix: String = "X") -> NonTerminal {
            let nt = NonTerminal(name: "\(prefix)\(ntCounter)")
            ntCounter += 1
            return nt
        }
        
        /// Reset the counter
        static func resetCounter() {
            ntCounter = 0
        }
        
        /// Group productions by their goal non-terminal
        static func groupProductions(_ productions: [Production]) -> [NonTerminal: [[Symbol]]] {
            var grouped: [NonTerminal: [[Symbol]]] = [:]
            
            for prod in productions {
                if grouped[prod.goal] == nil {
                    grouped[prod.goal] = []
                }
                grouped[prod.goal]?.append(prod.rule)
            }
            
            return grouped
        }
        
        /// Convert grouped productions back to Production array
        static func ungroupProductions(_ grouped: [NonTerminal: [[Symbol]]]) -> [Production] {
            var productions: [Production] = []
            
            for (goal, rules) in grouped {
                for rule in rules {
                    productions.append(Production(goal: goal, rule: rule))
                }
            }
            
            return productions
        }
    }
}
