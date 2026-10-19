//
//  GrammarForms.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2025/10/19.
//  Copyright © 2025 hakkabon software. All rights reserved.
//

import Foundation

/// A structural ordering key used only to make normal-form emission stable.
/// Length prefixes prevent values containing separators from colliding.
func normalFormTerminalOrderingKey(_ terminal: Terminal) -> String {
    switch terminal {
    case .string(let string):
        return "s\(string.count):\(string)"
    case .stringList(let list):
        return "l" + list.map { "\($0.count):\($0)" }.joined(separator: ",")
    case .characterRange(let range):
        return "c\(range.lowerBound)-\(range.upperBound)"
    case .regularExpression(let expression):
        return "r\(expression.pattern.count):\(expression.pattern)"
    case .meta(let meta):
        return "m\(meta.rawValue.count):\(meta.rawValue)"
    }
}

func normalFormRuleOrderingKey(_ rule: [Symbol]) -> String {
    rule.map { symbol in
        let kind: String
        let value: String
        switch symbol {
        case .nonTerminal(let nonterminal):
            kind = "n"
            value = nonterminal.name
        case .metaSymbol(let meta):
            kind = "m"
            value = meta.rawValue
        case .terminal(let terminal):
            kind = "t"
            value = normalFormTerminalOrderingKey(terminal)
        }
        return "\(kind)\(value.count):\(value)"
    }.joined(separator: "|")
}

public extension Grammar {
    
    /// Returns true, if the grammar is in chomsky normal form.
    ///
    /// A grammar is in chomsky normal form if all productions satisfy one of the following conditions:
    /// - A production generates exactly one terminal symbol
    /// - A production generates exactly two non-terminal symbols
    /// - A production generates an empty string and is generated from the start non-terminal
    var isInChomskyNormalForm: Bool {
        return productions.allSatisfy { production -> Bool in
            (production.isFinal && production.rule.count == 1)
            || (!production.isFinal && production.generatedNonTerminals.count == 2 && production.generatedTerminals.count == 0)
            || (production.rule.isEmpty && production.goal == start)
        }
    }

    /// Returns true if the grammar is in Greibach Normal Form.
    ///
    /// A grammar is in GNF if every production has the form  A → a α,
    /// where `a` is a terminal and α is a (possibly empty) sequence of non-terminals.
    var isInGreibachForm: Bool {
        return productions.allSatisfy { production in
            guard !production.rule.isEmpty else { return false }
            // First symbol must be a terminal
            guard production.rule[0].isTerminal else { return false }
            // All remaining symbols must be non-terminals
            return production.rule.dropFirst().allSatisfy { $0.isNonTerminal }
        }
    }

    /// If and only if there are no meta symbols left in the productions.
    var isInStandardNotation: Bool {
        return true
    }
}
