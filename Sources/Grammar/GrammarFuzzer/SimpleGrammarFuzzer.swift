//
//  SimpleGrammarFuzzer.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/12/17.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation

struct SimpleGrammarFuzzer {
 
    typealias Derivation = DerivationTree<NonTerminal, Terminal>
    
    let grammar: Grammar
    let goalProductions: [NonTerminal:[Production]]
    
    public init(grammar: Grammar) {
        self.grammar = grammar
        self.goalProductions = Dictionary(grouping: self.grammar.productions, by: { $0.goal })
    }
}
    
extension SimpleGrammarFuzzer {
    
    /// Produce a string from `grammar`.
    /// A very simple grammar fuzzer that starts with a start symbol (<start>) and then keeps on expanding it.
    /// To avoid expansion to infinite inputs, we place a limit (max_nonterminals) on the number of nonterminals.
    /// Furthermore, to avoid being stuck in a situation where we cannot reduce the number of symbols any further,
    /// we also limit the total number of expansion steps.
    /// - Parameters:
    ///   - maxNonterminals: the maximum number of nonterminals
    ///   - maxExpansionTrials: maximum # of attempts to produce a string
    ///   - log: print expansion progress if True
    /// - Returns: random expanded string using the given grammar.
    public func fuzz(maxNonterminals: Int = 5, maxExpansionTrials: Int = 50, log: Bool = true) -> [Symbol] {
        var term: [Symbol] = [Symbol.nonTerminal(grammar.start)]
        var expansionTrials = 0
        while countNonTerminals(symbols: term) > 0 {
            let (index,symbolToExpand) = randomNonTerminal(symbols: term)
            let productions = goalProductions[symbolToExpand]!
            if let production = productions.randomElement() {
                var newTerm = term
                newTerm.remove(at: index)
                newTerm.insert(contentsOf: production.rule, at: index)
                if countNonTerminals(symbols: newTerm) < maxNonterminals {
                    term = newTerm
                    if log {
                        print("\(symbolToExpand) -> \(toString(production.rule))".padding(toLength: 45, withPad: " ", startingAt: 0), toString(term))
                    }
                    expansionTrials = 0
                } else {
                    expansionTrials += 1
                    if expansionTrials >= maxExpansionTrials {
                        fatalError("Cannot expand " + String(describing: term))
                    }
                }
            }
        }
        return term
    }
    
    func randomNonTerminal(symbols: [Symbol]) -> (Int,NonTerminal) {
        var indexList: [(Int,NonTerminal)] = []
        for (index,symbol) in symbols.enumerated() {
            if case let .nonTerminal(nt) = symbol {
                indexList.append( (index,nt) )
            }
        }
        if let randomElement = indexList.randomElement() {
            return randomElement
        }
        fatalError()
    }

    func countNonTerminals(symbols: [Symbol]) -> Int {
        return symbols.reduce(0) { partialResult, symbol in
            if case .nonTerminal = symbol {
                return partialResult + 1
            }
            return partialResult
        }
    }

    func toString(_ symbols: [Symbol]) -> String {
        return symbols.map { "\($0)" }.joined(separator: " ")
    }
}
