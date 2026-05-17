//
//  GrammarRailroad.swift
//  BNF-Parser
//
//  Created by Ulf Akerstedt-Inoue on 2025/12/14.
//  Copyright © 2025 hakkabon software. All rights reserved.
//

import Foundation
import GrammarDiagram

/// Converts a parsed Context-Free Grammar tree into ASCII railroad diagrams
public struct GrammarToRailroad {
    
    public init() {}
    
    /// Generate ASCII railroad diagrams for all productions in the grammar
    public func generateDiagrams(_ syntaxNode: BnfExpression) -> String {
        let diagrams = convertSyntax(syntaxNode)
        var output = ""
        
        // Sort keys for deterministic output
        for name in diagrams.keys.sorted() {
            guard let element = diagrams[name] else { continue }
            
            output += "Production: \(name)\n"
            // Wrap the whole production in a 'Diagram' container for styling
            // @argument complex:
            // • false adds `|--` `--|` start/end markers
            // • true adds `╟--` `--╢` start/end markers
            let finalDiagram = diagram(element, complex: false)
            output += draw(finalDiagram)
            output += "\n\n"
        }
        
        return output
    }
    
    /// Generate ASCII railroad diagram for a single production
    public func generateDiagram(forProduction name: String, in syntaxNode: BnfExpression) -> String? {
        let diagrams = convertSyntax(syntaxNode)
        guard let element = diagrams[name] else { return nil }
        return draw(diagram(element, complex: true))
    }
    
    // MARK: - Conversion Logic
    
    /// Converts a Syntax Root into a dictionary of Name -> DiagramElement
    private func convertSyntax(_ node: BnfExpression) -> [String: DiagramElement] {
        var results = [String: DiagramElement]()
        
        switch node {
        case .syntax(let children):
            for child in children {
                if case .production(let name, let body) = child {
                    results[name] = convert(body)
                }
            }
        // Handle case where a single production is passed not wrapped in .syntax
        case .production(let name, let body):
            results[name] = convert(body)
        default:
            break
        }
        
        return results
    }
    
    /// Recursive converter from EBNF Node to DiagramElement
    private func convert(_ node: BnfExpression) -> DiagramElement {
        switch node {
            
        case .terminal(let name):
            return terminal(name)
            
        case .nonterminal(let name):
            return nonTerminal(name)
            
        // Sequences (A B C)
        case .sequence(let children):
            return sequence(children.map { convert($0) })
            
        // Alternatives (A | B | C)
        case .alternative(let children):
            return choice(children.map { convert($0) })
            
        // Optional [ ... ]
        case .optional(let expr):
            return optional(convert(expr))

        // Repetition { ... } (Zero or more)
        case .repetition(let expr):
            return optional(repeater(convert(expr)))

        // Grouping ( ... )
        case .grouping(let expr):
            return convert(expr)
            
        // Repetition One Plus { ... }+
        case .repetitionOnePlus(let expr):
            let element = convert(expr)
            return group(sequence([element, choice([element])]), label: "1..n")
            
        case .emptyStringSymbol:
            return skip()
            
        case .regex(let identifier, let pattern):
            return special("Regular expression:(\(identifier),\(pattern))")
            
        default:
            return special("Unknown diagram element")
        }
    }
}
