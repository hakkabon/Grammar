//
//  ChomskyForm.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/07.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation

extension Grammar {
/*
    class ChomskyNormalFormConverter {
        
        /// Convert grammar to Chomsky Normal Form
        /// - Parameter productions: Input productions
        /// - Returns: Productions in CNF
        public func convert(_ productions: [Production]) -> [Production] {
            GrammarUtils.resetCounter()
            
            var grouped = GrammarUtils.groupProductions(productions)
            
            // Step 1: Eliminate epsilon productions
            grouped = eliminateEpsilonProductions(grouped)
            
            // Step 2: Eliminate unit productions
            grouped = eliminateUnitProductions(grouped)
            
            // Step 3: Convert to CNF form
            grouped = convertToCNFForm(grouped)
            
            return GrammarUtils.ungroupProductions(grouped)
        }
        
        // MARK: - Step 1: Eliminate Epsilon Productions
        
        private func eliminateEpsilonProductions(_ grammar: [NonTerminal: [[Symbol]]]) -> [NonTerminal: [[Symbol]]] {
            
            // Find all nullable non-terminals
            var nullable = Set<NonTerminal>()
            var changed = true
            
            while changed {
                changed = false
                
                for (nt, rules) in grammar {
                    if nullable.contains(nt) { continue }
                    
                    for rule in rules {
                        // Check if rule is epsilon
                        if rule.count == 1 && rule[0].isEpsilon {
                            nullable.insert(nt)
                            changed = true
                            break
                        }
                        
                        // Check if all symbols in rule are nullable
                        if rule.allSatisfy({ symbol in
                            if let nt = symbol.nonTerminal {
                                return nullable.contains(nt)
                            }
                            return false
                        }) {
                            nullable.insert(nt)
                            changed = true
                            break
                        }
                    }
                }
            }
            
            // Generate new productions without epsilon
            var result: [NonTerminal: [[Symbol]]] = [:]
            
            for (nt, rules) in grammar {
                result[nt] = []
                
                for rule in rules {
                    // Skip epsilon productions
                    if rule.count == 1 && rule[0].isEpsilon {
                        continue
                    }
                    
                    // Generate all combinations by removing nullable symbols
                    let combinations = generateCombinations(rule: rule, nullable: nullable)
                    
                    for combo in combinations {
                        if !combo.isEmpty && !result[nt]!.contains(where: { $0 == combo }) {
                            result[nt]?.append(combo)
                        }
                    }
                }
            }
            
            return result
        }
        
        private func generateCombinations(rule: [Symbol], nullable: Set<NonTerminal>) -> [[Symbol]] {
            if rule.isEmpty {
                return [[]]
            }
            
            let first = rule[0]
            let rest = Array(rule.dropFirst())
            let restCombos = generateCombinations(rule: rest, nullable: nullable)
            
            var result: [[Symbol]] = []
            
            // Include combinations with first symbol
            for combo in restCombos {
                result.append([first] + combo)
            }
            
            // If first symbol is nullable, include combinations without it
            if let nt = first.nonTerminal, nullable.contains(nt) {
                result.append(contentsOf: restCombos)
            }
            
            return result
        }
        
        // MARK: - Step 2: Eliminate Unit Productions
        
        private func eliminateUnitProductions(_ grammar: [NonTerminal: [[Symbol]]])
            -> [NonTerminal: [[Symbol]]] {
            
            // Build unit pairs (A, B) where A =>* B
            var unitPairs: Set<String> = Set()
            
            // Initialize with reflexive pairs
            for nt in grammar.keys {
                unitPairs.insert("\(nt.name),\(nt.name)")
            }
            
            // Find all unit pairs
            var changed = true
            while changed {
                changed = false
                
                for (nt, rules) in grammar {
                    for rule in rules {
                        // Check if it's a unit production
                        if rule.count == 1, let target = rule[0].nonTerminal {
                            let pair = "\(nt.name),\(target.name)"
                            if !unitPairs.contains(pair) {
                                unitPairs.insert(pair)
                                changed = true
                            }
                            
                            // Transitivity: if (A, B) and (B, C) then (A, C)
                            for existing in unitPairs {
                                let parts = existing.split(separator: ",")
                                if parts[1] == nt.name {
                                    let newPair = "\(parts[0]),\(target.name)"
                                    if !unitPairs.contains(newPair) {
                                        unitPairs.insert(newPair)
                                        changed = true
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            // Build new grammar without unit productions
            var result: [NonTerminal: [[Symbol]]] = [:]
            
            for nt in grammar.keys {
                result[nt] = []
                
                for pair in unitPairs {
                    let parts = pair.split(separator: ",")
                    if parts[0] == nt.name {
                        let targetNT = NonTerminal(name: String(parts[1]))
                        
                        if let targetRules = grammar[targetNT] {
                            for rule in targetRules {
                                // Only add non-unit productions
                                if rule.count > 1 || !rule[0].isNonTerminal {
                                    if !result[nt]!.contains(where: { $0 == rule }) {
                                        result[nt]?.append(rule)
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            return result
        }
        
        // MARK: - Step 3: Convert to CNF Form
        
        private func convertToCNFForm(_ grammar: [NonTerminal: [[Symbol]]]) -> [NonTerminal: [[Symbol]]] {
            
            var result = grammar
            var terminalMap: [String: NonTerminal] = [:]
            
            // Replace terminals in productions of length > 1
            for (nt, rules) in result {
                var newRules: [[Symbol]] = []
                
                for rule in rules {
                    if rule.count == 1 {
                        newRules.append(rule)
                        continue
                    }
                    
                    var newRule: [Symbol] = []
                    for symbol in rule {
                        if symbol.isTerminal {
                            let termKey = terminalDescription(symbol)
                            
                            if terminalMap[termKey] == nil {
                                let newNT = GrammarUtils.generateNonTerminal(prefix: "T")
                                terminalMap[termKey] = newNT
                                result[newNT] = [[symbol]]
                            }
                            
                            newRule.append(.nonTerminal(terminalMap[termKey]!))
                        } else {
                            newRule.append(symbol)
                        }
                    }
                    newRules.append(newRule)
                }
                
                result[nt] = newRules
            }
            
            // Break down productions of length > 2
            var finalResult: [NonTerminal: [[Symbol]]] = [:]
            
            for (nt, rules) in result {
                finalResult[nt] = []
                
                for rule in rules {
                    if rule.count <= 2 {
                        finalResult[nt]?.append(rule)
                        continue
                    }
                    
                    // Break down: A -> B C D E becomes A -> B Y0, Y0 -> C Y1, Y1 -> D E
                    var current = rule[0]
                    
                    for i in 1..<rule.count {
                        if i == rule.count - 1 {
                            // Last pair
                            let newNT = GrammarUtils.generateNonTerminal(prefix: "Y")
                            
                            if i == 1 {
                                finalResult[nt]?.append([current, .nonTerminal(newNT)])
                            } else if let prevNT = current.nonTerminal {
                                if finalResult[prevNT] == nil {
                                    finalResult[prevNT] = []
                                }
                                finalResult[prevNT]?.append([rule[i - 1], .nonTerminal(newNT)])
                            }
                            
                            finalResult[newNT] = [[rule[i - 1], rule[i]]]
                        } else {
                            let newNT = GrammarUtils.generateNonTerminal(prefix: "Y")
                            
                            if i == 1 {
                                finalResult[nt]?.append([current, .nonTerminal(newNT)])
                            }
                            
                            current = .nonTerminal(newNT)
                        }
                    }
                }
            }
            
            return finalResult
        }
        
        private func terminalDescription(_ symbol: Symbol) -> String {
            if case .terminal(let t) = symbol {
                return t.description
            }
            return ""
        }
    }
*/
}


/*
 
 
    public struct Production: Codable {
        public let goal: NonTerminal
        public let rule: [Symbol]
        
        public init(goal: NonTerminal, rule: [Symbol]) {
            self.goal = goal
            self.rule = rule
        }
    }

    public enum Symbol: Codable {
        case terminal(Terminal)
        case nonTerminal(NonTerminal)
        case metaSymbol(MetaSymbol)
    }

    public struct NonTerminal: Codable, Hashable {
        public let name: String
        
        public init(name: String) {
            self.name = name
        }
    }

    public enum Terminal: Codable {
        case string(string: String)
        case characterRange(range: ClosedRange<Character>)
        case regularExpression(expression: NSRegularExpression)
        case meta(MetaTerminal)
    }

    public enum MetaSymbol: String, Codable {
        case epsilon = "ε"
        case endOfFile = "$"
    }

    public enum MetaTerminal: String, Codable {
        case epsilon = "ε"
        case endOfFile = "$"
    }

    // MARK: - Helper Extensions

    extension Symbol: Equatable {
        public static func == (lhs: Symbol, rhs: Symbol) -> Bool {
            switch (lhs, rhs) {
            case (.nonTerminal(let a), .nonTerminal(let b)):
                return a.name == b.name
            case (.metaSymbol(let a), .metaSymbol(let b)):
                return a == b
            case (.terminal(let a), .terminal(let b)):
                return a.description == b.description
            default:
                return false
            }
        }
    }

    extension Symbol: Hashable {
        public func hash(into hasher: inout Hasher) {
            switch self {
            case .nonTerminal(let nt):
                hasher.combine("NT")
                hasher.combine(nt.name)
            case .terminal(let t):
                hasher.combine("T")
                hasher.combine(t.description)
            case .metaSymbol(let m):
                hasher.combine("M")
                hasher.combine(m.rawValue)
            }
        }
    }

    extension Terminal {
        var description: String {
            switch self {
            case .string(let s):
                return s
            case .characterRange(let r):
                return "[\(r.lowerBound)-\(r.upperBound)]"
            case .regularExpression(let re):
                return re.pattern
            case .meta(let m):
                return m.rawValue
            }
        }
    }

    extension Symbol {
        var isTerminal: Bool {
            if case .terminal = self { return true }
            return false
        }
        
        var isNonTerminal: Bool {
            if case .nonTerminal = self { return true }
            return false
        }
        
        var isEpsilon: Bool {
            if case .metaSymbol(.epsilon) = self { return true }
            if case .terminal(.meta(.epsilon)) = self { return true }
            return false
        }
        
        var nonTerminal: NonTerminal? {
            if case .nonTerminal(let nt) = self {
                return nt
            }
            return nil
        }
    }

 
*/
