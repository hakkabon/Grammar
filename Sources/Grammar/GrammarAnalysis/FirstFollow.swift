//
//  FirstFollow.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/07.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation

extension Grammar {

    /// Returns true if this grammar is LL(1), otherwise false.
    /// - Parameters:
    ///   - first: first set
    ///   - follow: follow set
    /// - Returns: true if grammar is LL(1), otherwise false
    public func isLL1(first: [Symbol:Set<Symbol>], follow: [NonTerminal:Set<Symbol>]) -> Bool {
        let goalProductions = Dictionary(grouping: self.productions, by: { $0.goal })
        let eps: Symbol = .terminal(.meta(epsilon))
        let epsSet = Set(arrayLiteral: eps)

        func calculateFirst(_ symbols: [Symbol]) -> Set<Symbol> {
           var omega = Set<Symbol>()
           for symbol in symbols {
               omega = omega.union(first[symbol]!.subtracting(epsSet))
               if !first[symbol]!.contains(eps) { break }
           }
           if let symbol = symbols.last, first[symbol]!.contains(eps) {
               omega.formUnion(epsSet)
           }
           return omega
        }

        for A in nonTerminals {
            var set = Set<Symbol>()
            for p in goalProductions[A]! {
                var predict = calculateFirst(p.rule)
                if predict.contains(eps) {
                    predict.formUnion(follow[A]!)
                }
                if set.intersection(predict).isEmpty { return false }
                set.formUnion(predict)
            }
        }
        return true
    }
    
    ///
    /// Calculates the First and Follow sets for the entire grammar.
    ///
    public func firstAndFollow() -> ([Symbol: Set<Symbol>], [NonTerminal: Set<Symbol>]) {
        let eps: Symbol = .terminal(.meta(epsilon))
        let eof: Symbol = .terminal(.meta(endofile))

        var firstSets: [Symbol:Set<Symbol>] = nonTerminals.reduce(into: [:]) { $0[Symbol.nonTerminal($1)] = [] }
        firstSets.merge(terminals.map { (Symbol.terminal($0), [Symbol.terminal($0)]) }) { (_, new) in new }
        firstSets[eps] = Set(arrayLiteral: eps) // First of epsilon is epsilon itself
        
        func computeFirstOfSequence(_ sequence: [Symbol]) -> Set<Symbol> {
            var sequenceFirstSet: Set<Symbol> = Set()
            var allPreviousNullable = true
            
            for symbol in sequence {
                guard let firstOfSymbol = firstSets[symbol] else { continue }
                
                // Add all non-epsilon terminals from FIRST(symbol) to the result
                sequenceFirstSet.formUnion(firstOfSymbol.filter { $0 != eps })
                
                // If the symbol is not nullable, stop the process
                if !firstOfSymbol.contains(eps) {
                    allPreviousNullable = false
                    break
                }
            }
            
            // If all symbols in the sequence can derive epsilon, add epsilon to the result
            if allPreviousNullable {
                sequenceFirstSet.insert(eps)
            }
            
            return sequenceFirstSet
        }

        for production in productions {
            if !firstSets.keys.contains(.nonTerminal(production.goal)) {
                firstSets[.nonTerminal(production.goal)] = Set()
            }
            for symbol in production.rule {
                if case .terminal(_) = symbol {
                    if !firstSets.keys.contains(symbol) {
                        firstSets[symbol] = Set([symbol])
                    }
                }
            }
        }

        var changed = true
        while changed {
            changed = false
            
            for production in productions {
                let goal = production.goal
                let rhs = production.rule
                
                let oldSize = firstSets[.nonTerminal(goal)]!.count
                
                // Compute FIRST(RHS) and add it to FIRST(LHS)
                let firstOfRhs = computeFirstOfSequence(rhs)
                
                firstSets[.nonTerminal(goal)]!.formUnion(firstOfRhs)
                
                if firstSets[.nonTerminal(goal)]!.count != oldSize {
                    changed = true
                }
            }
        }

        // Remove the internal epsilon key as it's only used for computation
        firstSets.removeValue(forKey: eps)
        
        var followSets: [NonTerminal:Set<Symbol>] = nonTerminals.reduce(into: [:]) { $0[$1] = [] }

        // Initialize Follow Sets
        // Follow(Start) = { EOF }
        followSets[start] = [eof]
        
        // Ensure all NonTerminals have an empty set initially
        for prod in productions {
            if followSets[prod.goal] == nil {
                followSets[prod.goal] = []
            }
        }
        
        // Compute Follow Sets (Fixed-point iteration)
        changed = true
        while changed {
            changed = false
            
            for prod in productions {
                let A = prod.goal
                let rule = prod.rule
                
                // Rule: A -> X0 X1 ... Xn
                for (index, symbol) in rule.enumerated() {
                    // We only care about Follow sets for NonTerminals on the RHS
                    guard case .nonTerminal(let B) = symbol else { continue }
                    
                    // Beta is everything following B
                    let beta = Array(rule.dropFirst(index + 1))
                    
                    // Calculate First(Beta)
                    let firstBeta = first(of: beta, using: firstSets)
                    
                    // Add (First(Beta) - {ε}) to Follow(B)
                    let nonEpsilonFirst = firstBeta.filter { $0 != eps }
                    let countBefore = followSets[B]?.count ?? 0
                    
                    followSets[B, default: []].formUnion(nonEpsilonFirst)
                    
                    // If Beta is nullable (First(Beta) contains ε) OR Beta is empty,
                    // then Follow(A) is added to Follow(B)
                    if firstBeta.contains(eps) {
                        if let followA = followSets[A] {
                            followSets[B]?.formUnion(followA)
                        }
                    }
                    
                    if followSets[B]?.count != countBefore {
                        changed = true
                    }
                }
            }
        }
        
        return (firstSets, followSets)
    }
    
    /// The argument is a concatenation of terminals and nonterminals often found on the right
    /// hand side of a production. This is nontrivial because some of the leading nonterminals
    /// on the rhs can go to epsilon.
    /// Calculate first(ω1 ω2 ... ωn) = first(ω1) ∪ first(ω2) ∪ first(ω3) ∪ ... ∪ { λ },
    /// where terms are added based on if all of the terms before it in the rhs are nullable.
    /// - Parameters:
    ///   - symbols: concatenation of terminals and nonterminals
    /// - Returns: set of the First symbols of given concatenation of terminals and nonterminals
    public func first(of sequence: [Symbol], using firstSets: [Symbol:Set<Symbol>]) -> Set<Symbol> {
        let eps: Symbol = .terminal(.meta(epsilon))
        var sequenceFirstSet = Set<Symbol>()
        var allPreviousNullable = true

        for symbol in sequence {
            guard let firstOfSymbol = firstSets[symbol] else { continue }
            // Add all non-epsilon terminals from FIRST(symbol) to the result
            sequenceFirstSet.formUnion(firstOfSymbol.filter { $0 != eps })
            // If the symbol is not nullable, stop the process
            if !firstOfSymbol.contains(eps) {
                allPreviousNullable = false
                break
            }
        }
        // If all symbols in the sequence can derive epsilon, add epsilon to the result
        if allPreviousNullable {
            sequenceFirstSet.insert(eps)
        }
        return sequenceFirstSet
    }
    
    /// Compute FIRST set of a symbol sequence using pre-computed FIRST sets.
    /// Returns the set of terminals that can appear first, and whether the entire sequence is nullable.
    ///
    /// This method requires pre-computed FIRST sets. Use `computeFirst(of:using:)` instead
    /// if you already have the FIRST sets computed.
    ///
    /// Algorithm:
    ///   - For each symbol in the sequence:
    ///     - If it's a terminal, add it to the result and stop (not nullable)
    ///     - If it's a non-terminal, add its FIRST set (minus epsilon) to the result
    ///       - If the non-terminal is not nullable, stop (sequence not nullable)
    ///       - If the non-terminal is nullable, continue to the next symbol
    ///   - If we process all symbols and they're all nullable, the sequence is nullable
    ///
    public func first(of symbols: [Symbol]) -> (terminals: Set<Symbol>, nullable: Bool) {
        var result = Set<Symbol>()
        
        for symbol in symbols {
            switch symbol {
            case .terminal(let t) where t.isEmpty: continue
            case .terminal(_):
                result.insert(symbol)
                return (result, false)
            case .nonTerminal(let nt):
                let (f, canBeNull) = firstOfNonterminal(nt)
                 result.formUnion(f)
                 if !canBeNull { return (result, false) }
            case .metaSymbol(_): continue
            }
        }

        return (result, true)
    }

    private func firstOfNonterminal(_ nonterminal: NonTerminal) -> (Set<Symbol>, Bool) {
        let firstSets = firstSetFixpoint()
        return (firstSets[nonterminal, default: []], nullableNonTerminals.contains(nonterminal))
    }

    private func firstSetFixpoint() -> [NonTerminal: Set<Symbol>] {
        var firstSets: [NonTerminal: Set<Symbol>] = [:]
        var changed = true
        while changed {
            changed = false
            for production in productions {
                for symbol in production.rule {
                    switch symbol {
                    case .terminal(let t) where t.isEmpty:
                        continue
                    case .terminal:
                        if firstSets[production.goal, default: []].insert(symbol).inserted { changed = true }
                        break
                    case .nonTerminal(let nt):
                        let symbols = firstSets[nt, default: []]
                        for t in symbols {
                            if firstSets[production.goal, default: []].insert(t).inserted { changed = true }
                        }
                        if !nullableNonTerminals.contains(nt) { break }
                    case .metaSymbol: // These are the bnf/ebnf [], {}, (), |, etc. symbols
                        break
                    }
                }
            }
        }
        return firstSets
    }

    /// Compute FOLLOW sets for all nonterminals.
    ///
    /// Algorithm:
    ///   1. FOLLOW(Start) = { $ }
    ///   2. For each production A → α B β:
    ///      - Add FIRST(β) - {ε} to FOLLOW(B)
    ///      - If β is nullable (or empty), add FOLLOW(A) to FOLLOW(B)
    ///   3. Repeat step 2 until no changes occur (fixed-point iteration)
    ///
    public func followSets() -> [NonTerminal: Set<Symbol>] {
        let eof: Symbol = .terminal(.meta(endofile))
        
        // Pre-compute FIRST sets once
//        let (firstSets, _) = firstAndFollow()
        
        // Initialize FOLLOW sets
        var follow: [NonTerminal: Set<Symbol>] = [:]
        for nt in nonTerminals {
            follow[nt] = []
        }
        follow[start] = [eof]
        
        // Fixed-point iteration
        var changed = true
        while changed {
            changed = false
            
            for production in productions {
                let A = production.goal
                let rule = production.rule
                
                // For each non-terminal B in the rule
                for (index, symbol) in rule.enumerated() {
                    guard case .nonTerminal(let B) = symbol else { continue }
                    
                    // β is everything after B
                    let beta = Array(rule.dropFirst(index + 1))
                    
                    // Compute FIRST(β) using pre-computed sets
                    let (firstBeta, betaNullable) = first(of: beta)
                    
                    // Add FIRST(β) - {ε} to FOLLOW(B)
                    let oldSize = follow[B]?.count ?? 0
                    follow[B, default: []].formUnion(firstBeta)
                    
                    // If β is nullable (or empty), add FOLLOW(A) to FOLLOW(B)
                    if betaNullable {
                        if let followA = follow[A] {
                            follow[B, default: []].formUnion(followA)
                        }
                    }
                    
                    if follow[B]?.count != oldSize {
                        changed = true
                    }
                }
            }
        }
        
        return follow
    }
}
