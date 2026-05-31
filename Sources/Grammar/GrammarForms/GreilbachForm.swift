//
//  GreilbachForm.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2024/01/04.
//  Copyright © 2024 hakkabon software. All rights reserved.
//

import Foundation

extension Grammar {

/*
    class GreibachNormalFormConverter {
        
        /// Convert grammar to Greibach Normal Form
        /// - Parameter productions: Input productions
        /// - Returns: Productions in GNF
        public func convert(_ productions: [Production]) -> [Production] {
            GrammarUtils.resetCounter()
            
            var grouped = GrammarUtils.groupProductions(productions)
            
            // Step 1: Eliminate epsilon productions
            grouped = eliminateEpsilonProductions(grouped)
            
            // Step 2: Eliminate unit productions
            grouped = eliminateUnitProductions(grouped)
            
            // Step 3: Eliminate left recursion and convert to GNF
            grouped = convertToGNFForm(grouped)
            
            return GrammarUtils.ungroupProductions(grouped)
        }
        
        // MARK: - Epsilon and Unit Production Elimination (same as CNF)
        
        private func eliminateEpsilonProductions(_ grammar: [NonTerminal: [[Symbol]]]) -> [NonTerminal: [[Symbol]]] {
            // Same implementation as CNF converter
            let cnfConverter = ChomskyNormalFormConverter()
            return cnfConverter.eliminateEpsilonProductions(grammar)
        }
        
        private func eliminateUnitProductions(_ grammar: [NonTerminal: [[Symbol]]]) -> [NonTerminal: [[Symbol]]] {
            // Same implementation as CNF converter
            let cnfConverter = ChomskyNormalFormConverter()
            return cnfConverter.eliminateUnitProductions(grammar)
        }
        
        // MARK: - Convert to GNF Form
        
        private func convertToGNFForm(_ grammar: [NonTerminal: [[Symbol]]]) -> [NonTerminal: [[Symbol]]] {
            
            var result = grammar
            let nts = Array(grammar.keys.sorted { $0.name < $1.name })
            
            // Step 1: Order non-terminals and eliminate left recursion
            for i in 0..<nts.count {
                let ai = nts[i]
                guard var aiRules = result[ai] else { continue }
                
                // Replace Ai -> Aj γ where j < i
                var newRules: [[Symbol]] = []
                
                for rule in aiRules {
                    if let firstNT = rule.first?.nonTerminal,
                       let j = nts.firstIndex(of: firstNT),
                       j < i {
                        // Replace with all productions of Aj
                        if let ajRules = result[firstNT] {
                            for ajRule in ajRules {
                                newRules.append(ajRule + Array(rule.dropFirst()))
                            }
                        }
                    } else {
                        newRules.append(rule)
                    }
                }
                
                result[ai] = newRules
                
                // Eliminate immediate left recursion
                result = eliminateImmediateLeftRecursion(result, for: ai)
            }
            
            // Step 2: Ensure all productions start with a terminal
            result = ensureTerminalFirst(result)
            
            return result
        }
        
        private func eliminateImmediateLeftRecursion(_ grammar: [NonTerminal: [[Symbol]]], for nt: NonTerminal) -> [NonTerminal: [[Symbol]]] {
            
            var result = grammar
            guard let rules = result[nt] else { return result }
            
            var recursive: [[Symbol]] = []
            var nonRecursive: [[Symbol]] = []
            
            for rule in rules {
                if let firstNT = rule.first?.nonTerminal, firstNT == nt {
                    // A -> A α, store α
                    recursive.append(Array(rule.dropFirst()))
                } else {
                    nonRecursive.append(rule)
                }
            }
            
            if !recursive.isEmpty {
                let newNT = GrammarUtils.generateNonTerminal(prefix: "Z")
                
                // A -> β A' for each non-recursive production
                result[nt] = nonRecursive.map { $0 + [.nonTerminal(newNT)] }
                
                // A' -> α A' | ε for each recursive production
                var newNTRules: [[Symbol]] = []
                for alpha in recursive {
                    newNTRules.append(alpha + [.nonTerminal(newNT)])
                }
                newNTRules.append([.terminal(.meta(.eps))])
                
                result[newNT] = newNTRules
            }
            
            return result
        }
        
        private func ensureTerminalFirst(_ grammar: [NonTerminal: [[Symbol]]]) -> [NonTerminal: [[Symbol]]] {
            
            var result: [NonTerminal: [[Symbol]]] = [:]
            var maxIterations = 100  // Prevent infinite loops
            
            for (nt, rules) in grammar {
                result[nt] = []
                
                for rule in rules {
                    if rule.isEmpty || rule[0].isEpsilon {
                        result[nt]?.append(rule)
                    } else if rule[0].isTerminal {
                        result[nt]?.append(rule)
                    } else if let firstNT = rule[0].nonTerminal {
                        // Replace A -> B α with A -> γ α for all B -> γ where γ starts with terminal
                        var expanded = expandToTerminal(
                            firstNT: firstNT,
                            rest: Array(rule.dropFirst()),
                            grammar: grammar,
                            depth: 0,
                            maxDepth: maxIterations
                        )
                        
                        // If we couldn't expand, keep the original rule
                        if expanded.isEmpty {
                            expanded = [rule]
                        }
                        
                        result[nt]?.append(contentsOf: expanded)
                    }
                }
            }
            
            return result
        }
        
        private func expandToTerminal(firstNT: NonTerminal, rest: [Symbol], grammar: [NonTerminal: [[Symbol]]], depth: Int, maxDepth: Int) -> [[Symbol]] {
            
            if depth >= maxDepth { return [] }
            guard let rules = grammar[firstNT] else { return [] }
            var result: [[Symbol]] = []
            
            for rule in rules {
                if rule.isEmpty { continue }
                
                switch rule[0] {
                case .terminal(let terminal):
                    result.append(rule + rest)
                case .nonTerminal(let nonTerminal):
                    let expanded = expandToTerminal(
                        firstNT: nonTerminal,
                        rest: Array(rule.dropFirst()) + rest,
                        grammar: grammar,
                        depth: depth + 1,
                        maxDepth: maxDepth
                    )
                    result.append(contentsOf: expanded)
                default:
                    break
                }
//                if rule[0].isTerminal || rule[0].isEpsilon {
//                    result.append(rule + rest)
//                } else if let nextNT = rule[0].nonTerminal {
//                    let expanded = expandToTerminal(
//                        firstNT: nextNT,
//                        rest: Array(rule.dropFirst()) + rest,
//                        grammar: grammar,
//                        depth: depth + 1,
//                        maxDepth: maxDepth
//                    )
//                    result.append(contentsOf: expanded)
//                }
            }
            
            return result
        }
    }
*/
    
}
 

/*

  // MARK: - Example Usage

  func exampleUsage() {
      // Create a simple grammar: S -> A B | a, A -> a A | ε, B -> b B | b
      let s = NonTerminal(name: "S")
      let a = NonTerminal(name: "A")
      let b = NonTerminal(name: "B")
      
      let termA = Symbol.terminal(.string(string: "a"))
      let termB = Symbol.terminal(.string(string: "b"))
      let epsilon = Symbol.metaSymbol(.epsilon)
      
      let productions = [
          Production(goal: s, rule: [.nonTerminal(a), .nonTerminal(b)]),
          Production(goal: s, rule: [termA]),
          Production(goal: a, rule: [termA, .nonTerminal(a)]),
          Production(goal: a, rule: [epsilon]),
          Production(goal: b, rule: [termB, .nonTerminal(b)]),
          Production(goal: b, rule: [termB])
      ]
      
      // Convert to CNF
      let cnfConverter = ChomskyNormalFormConverter()
      let cnfProductions = cnfConverter.convert(productions)
      
      print("=== Chomsky Normal Form ===")
      for prod in cnfProductions {
          let ruleStr = prod.rule.map { symbol -> String in
              switch symbol {
              case .nonTerminal(let nt): return nt.name
              case .terminal(let t): return t.description
              case .metaSymbol(let m): return m.rawValue
              }
          }.joined(separator: " ")
          print("\(prod.goal.name) -> \(ruleStr)")
      }
      
      // Convert to GNF
      let gnfConverter = GreibachNormalFormConverter()
      let gnfProductions = gnfConverter.convert(productions)
      
      print("\n=== Greibach Normal Form ===")
      for prod in gnfProductions {
          let ruleStr = prod.rule.map { symbol -> String in
              switch symbol {
              case .nonTerminal(let nt): return nt.name
              case .terminal(let t): return t.description
              case .metaSymbol(let m): return m.rawValue
              }
          }.joined(separator: " ")
          print("\(prod.goal.name) -> \(ruleStr)")
      }
  }

  // Uncomment to run example
  // exampleUsage()
  
 
*/
