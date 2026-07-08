//
//  GrammarExpression.swift
//  BNF-Parser
//
//  Created by Ulf Akerstedt-Inoue on 2019/01/08.
//  Copyright © 2019 hakkabon software. All rights reserved.
//

import Foundation
import TerminalColors

/// This recursively defined enum models the BNF/EBNF/WSN classification of Context
/// Free Grammars.
/// Mapping of `token type`, often called `token class`, to BNF classification are as
/// follows
/// - `Nonterminals` correspond to .identifier or keywords tokens.
/// - `Terminals` may be { .symbol | .literals | .number }
/// - `Punctuation` corresponds to meta symbols used by BNF and EBNF grammars.
///
/// The `BnfExpression` is extended with structured EBNF constructs like
/// - sequence              A B C  or  A, B, C, (only ebnf)
/// - choice                A | B | C
/// - optional              [ ... ]
/// - repetition            { ... }
/// - grouping              ( ... )
///
///TODO: There are still a few ebnf constructs not covered yet.

public indirect enum BnfExpression: Codable, Equatable, Hashable {
    // Structure
    case syntax([BnfExpression])
    case production(String, BnfExpression)

    // Structure nodes (EBNF constructs)
    case sequence([BnfExpression])           // A B C (implicit) or A, B, C (explicit)
    case alternative([BnfExpression])        // multiple choices
    case optional(BnfExpression)             // [...]
    case repetition(BnfExpression)           // {...}
    case repetitionOnePlus(BnfExpression)    // {...}+
    case grouping(BnfExpression)             // (...)
    
    // Terminals and NonTerminals
    case terminal(String)
    case nonterminal(String)

    // Range expressions
    case range(String,String,String)        // range of characters, like 'a'..'z' or "\u{0400}" .. "\u{04FF}"
    
    // List expressions
    case list(String,[String])              // EMOTICONS ::= '\u{1F600}' | '\u{1F602}' ;

    // Regular expressions
    case regex(String,String)

    // Empty string symbol, typically called epsilon
    case empty(String)

//    // Meta terminal: eof (end-of-file)
//    case endOfFileSymbol(String)

    // Start symbol in grammar (non-terminal)
    case start(String)
}

extension BnfExpression: CustomStringConvertible {
    
    public var description: String {
        return TreePrinter.printTree(self)
    }
}

// MARK: - Tree outline using indentation for pretty printing

extension BnfExpression {
    
    private func prettyPrint(indent: Int) -> String {
        let spaces = String(repeating: "  ", count: indent)
        
        switch self {
        case .syntax(let list):
            return "\(spaces)Syntax\n" + list.map { $0.prettyPrint(indent: indent + 1) }.joined(separator: "\n")
            
        case .production(let name, let expr):
            return "\(spaces)Production: \(name)\n\(expr.prettyPrint(indent: indent + 1))"
            
        case .sequence(let list):
            let children = list.map { $0.prettyPrint(indent: indent + 1) }.joined(separator: "\n")
            return "\(spaces)Sequence\n\(children)"
            
        case .alternative(let list):
            let children = list.map { $0.prettyPrint(indent: indent + 1) }.joined(separator: "\n")
            return "\(spaces)Alternative\n\(children)"
            
        case .optional(let expression):
            return "\(spaces)Optional\n\(expression.prettyPrint(indent: indent + 1))"
        case .repetition(let expression):
            return "\(spaces)Repetition\n\(expression.prettyPrint(indent: indent + 1))"
        case .repetitionOnePlus(let expression):
            return "\(spaces)RepetitionOnePlus\n\(expression.prettyPrint(indent: indent + 1))"
        case .grouping(let expression):
            return "\(spaces)Grouping\n\(expression.prettyPrint(indent: indent + 1))"

        case .terminal(let val): return "\(spaces)\"\(val)\""
        case .nonterminal(let val): return "\(spaces)<\(val)>"
        default: return "\(spaces)\(self)"
        }
    }
}

// MARK: - Visual tree structure for pretty printing

struct TreePrinter {
    
    // Define reusable formats
    private static let branchColor = TerminalColor(fg: .blue)
    private static let leafColor = TerminalColor(fg: .green)
    private static let nodeColor = TerminalColor(.bold)

    static func printTree(_ node: BnfExpression, indentation: String = "", isLast: Bool = true) -> String {
        let (label, children) = extractNodeData(node)
        
        // Root label with indentation.
        var result = "\(indentation, color: branchColor)\(label, color: nodeColor)\n"
        
        // Everything else except the root node.
        for (index, child) in children.enumerated() {
            let isLastChild = index == children.count - 1
            result += printChildren(child, prefix: indentation, isLast: isLastChild)
        }
        return result
    }

    static func printChildren(_ node: BnfExpression, prefix: String = "", isLast: Bool = true) -> String {
        let (label, children) = extractNodeData(node)
        
        // Current Line: Handle the branch marker
        let marker = (isLast ? "└── " : "├── ")
        let styledLabel = children.isEmpty ? leafColor : nodeColor
        var result = "\(prefix, color: branchColor)\(marker, color: branchColor)\(label, color: styledLabel)\n"

        let nextPrefix = prefix + (isLast ? "    " : "│   ")
        for (index, child) in children.enumerated() {
            let isLastChild = index == children.count - 1
            result += printChildren(child, prefix: nextPrefix, isLast: isLastChild/*, isRoot: false*/)
        }
        return result
    }
    
    private static func extractNodeData(_ node: BnfExpression) -> (String, [BnfExpression]) {
        switch node {
        case .syntax(let list):             return ("Syntax Root", list)
        case .production(let name, let e):  return ("Production: \(name)", [e])
        case .sequence(let list):           return ("Sequence", list)
        case .alternative(let list):        return ("Alternative", list)
        case .optional(let e):              return ("Optional [?]", [e])
        case .repetition(let e):            return ("Repetition {*}", [e])
        case .repetitionOnePlus(let e):     return ("Repetition {+}", [e])
        case .grouping(let e):              return ("Group (...)", [e])
        case .terminal(let val):            return ("'\(val)'", [])
        case .nonterminal(let val):         return ("<\(val)>", [])
        case .range(let id, let a, let b):  return ("Range /\(id)/ /\(a)..\(b)/", [])
        case .list(let id, let list):       return ("List /\(id)/ /\(list)/", [])
        case .regex(let id, let p):         return ("Regex /\(id)/ /\(p)/", [])
        case .empty(let s):                 return ("Empty (\(s))", [])
//        case .endOfFileSymbol(let s):       return ("Eof (\(s))", [])
        case .start(let s):                 return ("Start (\(s))", [])
        }
    }
}

