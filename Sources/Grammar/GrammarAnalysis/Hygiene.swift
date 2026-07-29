//
//  Hygiene.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/07.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation
 
extension Grammar {

    /// Non-terminals which cannot be reached from the start non-terminal
    /// 2.9.5.2 Removing Unreachable Non-Terminals
    /// [1] Parsing Techniques
    public var unreachableNonTerminals: Set<NonTerminal> {
        let productionSet: Set<Production> = Set(productions)
        let reachableProductions = Grammar.eliminateUnusedProductions(productions: productions, start: start).collect(Set.init)
        return productionSet.subtracting(reachableProductions).map{ $0.goal }.collect(Set.init)
    }
    
    /// 2.9.5.1 Removing Non-Productive Rules
    /// [1] Parsing Techniques
    public static func eliminateUnusedProductions(productions: [Production], start: NonTerminal) -> [Production] {
        let nonTerminalProductions = Dictionary(grouping: productions, by: { $0.goal })
        
        func mark(nonTerminal: NonTerminal, visited: Set<NonTerminal>) -> Set<NonTerminal> {
            if visited.contains(nonTerminal) {
                return visited
            }
            
            let newVisited = visited.union([nonTerminal])
            let reachableProductions = nonTerminalProductions[nonTerminal] ?? []
            return reachableProductions.reduce(newVisited) { partialVisited, production -> Set<NonTerminal> in
                production.generatedNonTerminals.reduce(partialVisited) { partial, n -> Set<NonTerminal> in
                    mark(nonTerminal: n, visited: partial)
                }
            }
        }
        
        let reachableNonTerminals = mark(nonTerminal: start, visited: [])
        
        return productions.filter { production -> Bool in
            reachableNonTerminals.contains(production.goal)
        }
    }

    /// The next trouble-makers to be eliminated are the unit rules, that is, rules of the form A → B.
    /// It is important to realize that, if such a rule A → B is used in a derivation, it must be
    /// followed at some point by the use of a rule B → α. Therefore, if we have a rule A → B, and the
    /// rules for B are
    /// B → α1 | α2 | ··· | αn,
    /// we can replace the rule A → B with
    /// A → α1 | α2 | ··· | αn.
    /// 4.2.3.2 Eliminating Unit Rules
    /// [1] Parsing Techniques
    public static func eliminateUnitRules(productions: [Production]) -> [Production] {
        let nonTerminalProductions = Dictionary(grouping: productions, by: { $0.goal })
        
        func findNonChainProduction(from start: Production, visited: Set<NonTerminal>, path: [NonTerminal]) -> [(Production, [NonTerminal])] {
            if start.isFinal || start.generatedNonTerminals.count != 1 {
                return [(start, path)]
            } else if visited.contains(start.goal) {
                return []
            }
            
            let nonTerminal = start.generatedNonTerminals[0]
            let reachableProductions = nonTerminalProductions[nonTerminal] ?? []
            
            return reachableProductions.flatMap{findNonChainProduction(from: $0, visited: visited.union([start.goal]), path: path + [nonTerminal])}
        }
        
        return productions.flatMap { production -> [Production] in
            let nonChainProductions = findNonChainProduction(from: production, visited: [], path: [])
            return nonChainProductions.map { element -> Production in
                let (p, chain) = element
                return Production(goal: production.goal, rule: p.rule, chain: chain)
            }
        }
    }

    /// 4.2.3.1 Eliminating 𝛆-rules
    /// [1] Parsing Techniques
    public static func eliminateEmpty(productions: [Production], start: NonTerminal) -> [Production] {
        let groupedProductions = Dictionary(grouping: productions, by: { $0.goal} )
        
        func generatesEmpty(_ nonTerminal: NonTerminal, path: Set<NonTerminal>) -> Bool {
            if path.contains(nonTerminal) {
                return false
            }
            
            let directProductions = groupedProductions[nonTerminal, default: []]
            return directProductions.contains { production -> Bool in
                if production.rule.isEmpty {
                    return true
                }
                return production.generatedNonTerminals.count == production.rule.count
                    && production.generatedNonTerminals.allSatisfy { pattern -> Bool in
                        generatesEmpty(pattern, path: path.union([nonTerminal]))
                    }
            }
        }
        
        func generatesNonEmpty(_ nonTerminal: NonTerminal, path: Set<NonTerminal>) -> Bool {
            if path.contains(nonTerminal) {
                return false
            }
            
            let directProductions = groupedProductions[nonTerminal, default: []]
            return directProductions.contains { production -> Bool in
                if !production.generatedTerminals.isEmpty {
                    return true
                }
                return production.generatedNonTerminals.contains { pattern -> Bool in
                    generatesNonEmpty(pattern, path: path.union([nonTerminal]))
                }
            }
        }
        
        let result = Dictionary(uniqueKeysWithValues: groupedProductions.keys.map { key -> (NonTerminal, (generatesEmpty: Bool, generatesNonEmpty: Bool)) in
            (key, (generatesEmpty: generatesEmpty(key, path: []), generatesNonEmpty: generatesNonEmpty(key, path: [])))
        })
        
        let updatedProductions = productions.flatMap { production -> [Production] in
            if production.rule.isEmpty && production.goal != start {
                return []
            }
            if production.isFinal {
                return [production]
            }
            let produced = production.rule.reduce([[]]) { (partialResult, symbol) -> [[Symbol]] in
                if case .nonTerminal(let nonTerminal) = symbol {
                    let (empty, nonEmpty) = result[nonTerminal] ?? (false, true)
                    
                    if !nonEmpty {
                        return partialResult
                    } else if !empty {
                        return partialResult.map {$0 + [symbol]}
                    } else {
                        return partialResult + partialResult.map {$0 + [symbol]}
                    }
                } else {
                    return partialResult.map {$0 + [symbol]}
                }
            }
            return produced.compactMap { sequence -> Production? in
                guard !sequence.isEmpty || production.goal == start else {
                    return nil
                }
                return Production(goal: production.goal, rule: sequence)
            }
        }
        return updatedProductions
    }
    
    /// Searches grammar for nonterminals without any production rule.
    /// 2.9.1 Undefined Non-Terminals
    /// [1] Parsing Techniques
    public var undefinedNonterminals: Set<NonTerminal> {
        let nonTerminals = Set( productions.flatMap { $0.generatedNonTerminals } )
        let goalTerminals = Set( productions.map { $0.goal } )

        // check undefined Nonterminals
        return nonTerminals.subtracting(goalTerminals)
    }
    
/*
    /// A rule is productive if its right-hand side consists of symbols all of
    /// which are productive. Terminal symbols are productive since they produce
    /// terminals and empty is productive since it produces the empty string. A
    /// non-terminal is productive if there is a productive rule for it.
    /// Iterate over all productions until set of 'productive symbols' does not
    /// grow anymore. Production A → α B β is non-productive as long as one
    /// nonterminal is non-productive.
    /// 2.9.5.1 Removing Non-Productive Rules
    /// [1] Parsing Techniques
    func unproductiveRuleCheck() {
        // marks productive grammar rules as true
        var productiveRule: [ProductionRule:Bool] = [:]
        
        // marks productive grammar nonterminals as true
        var productiveSymbol: [String:Bool] = [:]
        
        // initialize all productions in the grammar to non-productive
        for p in productions { productiveRule[p] = false }
        
        // initialize all nonterminals in the grammar to non-productive
        for nt in nonterminals { productiveSymbol[nt] = false }
        
        // loop until set of productive symbols does not grow anymore
        var n: Int = 0
        var m: Int = 0
        repeat {
            n = m
            for p in productions {
                var productive = true
                for s in p.rhs {
                    // all terminals are productive A → a including A → ε
                    if isTerminal(symbol: s) || s == Constant.eps { continue }
                    // production A → α B β is non-productive as long as one
                    // nonterminal is non-productive, here B=s
                    if isNonterminal(symbol: s) {
                        if !productiveSymbol[s]! { productive = false }
                    }
                }
                productiveRule[p] = productive
            }
            
            // collect any new productive nonterminals
            for p in productions {
                if productiveRule[p]! { productiveSymbol[p.lhs] = true }
            }
            // calculate current cardinality of productive symbols set
            m = 0
            for symbol in productiveSymbol.keys {
                if productiveSymbol[symbol]! { m += 1 }
            }
            
            // finish criteria: productive symbols set is not growing anymore
        } while (n < m)
        
        // production rules result
        //if (n>0) writeln("Grammar contains unproductive production rules!");
        for p in productiveRule.keys {
            if !productiveRule[p]! {
                p.productive = false;
                print("production '\(p)' is a non-productive rule - consider fixing.")
            }
        }
    }

    /// A non-terminal is called reachable or accessible if there exists at least
    /// one sentential form, derivable from the start symbol, in which it occurs.
    /// So a non-terminal A is reachable if S ⇒* αAβ for some α and β.
    /// Traverse grammar foreach nonterminal symbol starting with goal symbol and
    /// for each rule in the grammar of the form A → α with A marked, all non-
    /// terminals in α are marked
    ///
    /// Reference:
    /// 2.9.5.2 Removing Unreachable Non-Terminals
    /// [1] Parsing Techniques
    func unreachableNonterminalCheck() {
        // marks reachable grammar nonterminals as true
        var reachableSymbol: [String:Bool] = [:]
        
        // initialize all nonterminals in the grammar to non-reachable
        for symbol in nonterminals { reachableSymbol[symbol] = false }
        
        // start symbol is reachable
        reachableSymbol[S] = true
        
        // loop until set of reachable symbols does not grow anymore
        var n: Int = 0
        var m: Int = 0
        repeat {
            n = m
            for p in productions {
                if reachableSymbol[p.lhs]! {
                    for s in p.rhs {
                        if isNonterminal(symbol: s) {
                            reachableSymbol[s] = true
                        }
                    }
                }
            }
        
            // calculate current cardinality of reachable symbols set
            m = 0
            for symbol in reachableSymbol.keys {
                if reachableSymbol[symbol]! { m += 1 }
            }
         
            // finish criteria: reachable symbols set is not growing anymore
        } while (n < m)
        
        // non reachable symbols result
        //if (n>0) writeln("Grammar contains unreachable nonterminals!");
        for symbol in reachableSymbol.keys {
            if !reachableSymbol[symbol]! {
                print("unreachable nonterminal ' \(symbol)' - consider fixing.")
            }
        }
    }
    
    /// Check for circular definitions.
    func checkCycles() {
    }
 
*/

}
