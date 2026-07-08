//
//  GrammarPrettyPrinter.swift
//  BNF-Parser
//
//  Created by Ulf Akerstedt-Inoue on 2026/01/09.
//  Copyright © 2019 hakkabon software. All rights reserved.
//

import Foundation

public struct GrammarPrettyPrinter {
    
    public struct Configuration {
        public var definitionOperator: String = "::=" // or "="
        public var terminator: String = ";"           // or "." or ""
        public var indentWidth: Int = 4
        
        public init() {}
    }
    
    private let config: Configuration
    
    public init(config: Configuration = Configuration()) {
        self.config = config
    }
    
    // MARK: - Public API
    
    public func print(_ node: BnfExpression) -> String {
        return visit(node, contextPrecedence: .lowest)
    }
    
    // MARK: - Precedence Handling
    
    /// Defines binding strength to determine when to add parentheses automatically.
    private enum Precedence: Int, Comparable {
        case lowest = 0         // Start context
        case alternative = 1    // A | B
        case sequence = 2       // A B
        case suffix = 3         // { }, [ ]
        case atom = 4           // "term", <nonterm>, ( )
        
        static func < (lhs: Precedence, rhs: Precedence) -> Bool {
            return lhs.rawValue < rhs.rawValue
        }
    }
    
    // MARK: - Recursive Visitor
    
    private func visit(_ node: BnfExpression, contextPrecedence: Precedence) -> String {
        switch node {
            
        // Root - List of production
        case .syntax(let productions):
            // Join all productions with double newlines
            return productions
                .map { visit($0, contextPrecedence: .lowest) }
                .joined(separator: "\n\n")
            
        // Production Rule
        case .production(let name, let expr):
            let def = config.definitionOperator
            let term = config.terminator
            // We force lowest precedence for the RHS so it doesn't wrap in parens
            let rhs = visit(expr, contextPrecedence: .lowest)
            
            // Nice formatting:
            // name ::=
            //     expression ;
            let indent = String(repeating: " ", count: config.indentWidth)
            return "\(name) \(def)\n\(indent)\(rhs) \(term)"
            
        // Alternatives ( A | B )
        case .alternative(let items):
            let text = items
                .map { visit($0, contextPrecedence: .alternative) }
                .joined(separator: " | ")
            
            return maybeWrap(text, current: .alternative, context: contextPrecedence)
            
        // Sequences ( A B )
        case .sequence(let items):
            let text = items
                .map { visit($0, contextPrecedence: .sequence) }
                .joined(separator: " ")
            
            return maybeWrap(text, current: .sequence, context: contextPrecedence)
            
        // Encapsulated Structures
        // These effectively reset precedence inside them because they have explicit delimiters
        
        case .optional(let expr):
            return "[ " + visit(expr, contextPrecedence: .lowest) + " ]"
            
        case .repetition(let expr):
            return "{ " + visit(expr, contextPrecedence: .lowest) + " }"
            
        case .repetitionOnePlus(let expr):
            return "{ " + visit(expr, contextPrecedence: .lowest) + " }+" // Extended EBNF style
            
        case .grouping(let expr):
            return "( " + visit(expr, contextPrecedence: .lowest) + " )"
            
        case .terminal(let value):
            guard let meta = MetaTerminal(rawValue: value) else {
                // The string did not match any of the meta terminal strings,
                // therefore it must be an ordinaly terminal.
                return quote(value)
            }
            return "\(meta)"
            
        case .nonterminal(let value):
            // Check if it needs angle brackets based on convention,
            // usually EBNF uses plain identifiers, BNF uses <>.
            // Let's stick to the raw name for EBNF.
            return value
        
        case .range(let id, let a, let b):
            return "\(id) : \(a)..\(b)"
            
        case .list(let id, let list):
            return "\(id) : \(list)"
            
        case .regex(let id, let pattern):
            return "\(id) : /\(pattern)/"
            
        case .empty(let symbol):
            return "epsilon: \(symbol)"

//        case .endOfFileSymbol(let symbol):
//            return "EOF: \(symbol)"

        case .start(let start):
            return "Start synbol: \(start)"
        }
    }
    
    // MARK: - Helpers
    
    /// Wraps the content in ( ... ) if the current node binds looser than the parent expects.
    private func maybeWrap(_ text: String, current: Precedence, context: Precedence) -> String {
        // Example: If context is .sequence (parent wants Sequence),
        // and current is .alternative (we are A | B),
        // Alternative < Sequence, so we MUST wrap -> (A | B)
        if current < context {
            return "( \(text) )"
        }
        return text
    }
    
    /// Smart quoting logic
    private func quote(_ str: String) -> String {
        if str.contains("\"") {
            return "'\(str)'"
        } else {
            return "\"\(str)\""
        }
    }
}
