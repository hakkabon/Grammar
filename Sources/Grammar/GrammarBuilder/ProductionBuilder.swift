//
//  ProductionBuilder.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/21.
//

import Foundation

/*
public struct Rule {
    /// Starting pattern
    public let goal: NonTerminal
    
    /// Symbols produced by substitution from the goal non terminal.
    public let rule: [Symbol]

    public init(goal: NonTerminal, rule: [Symbol]) {
        self.goal = goal
        self.rule = rule
    }

    public init(goal: NonTerminal, @ProductionBuilder builder: () -> ProductionResult) {
        self.goal = goal

        switch builder() {
        case let .con(symbols):
            self.rule = symbols
        case let .alt(symbols):
            self.rule = symbols.flatMap { $0 }
        }
    }
}

extension Rule {
    func generate(goal: NonTerminal, @ProductionBuilder builder: () -> ProductionResult) -> [Production] {
        switch builder() {
        case let .con(symbols):
            return [Production(goal: goal, rule: symbols)]
        case let .alt(symbols):
            return symbols.compactMap { rule in
                return Production(goal: goal, rule: rule)
            }
        }
    }
}
*/
