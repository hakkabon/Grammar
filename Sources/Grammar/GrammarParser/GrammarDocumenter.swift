//
//  GrammarDocumenter.swift
//  BNF-Parser
//
//  Created by Ulf Akerstedt-Inoue on 2026/01/11.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

public struct GrammarDocumenter {
    
    public struct Configuration {
        public var showSeparator: Bool = true
        public var separatorChar: Character = "-"
        public var separatorWidth: Int = 80
        public var verticalSpacing: Int = 1
        
        // Pass-through configs
        public var printerConfig = GrammarPrettyPrinter.Configuration()
        
        public init() {}
    }
    
    private let config: Configuration
    private let prettyPrinter: GrammarPrettyPrinter
    private let diagramGenerator: GrammarToRailroad
    
    public init(config: Configuration = Configuration()) {
        self.config = config
        self.prettyPrinter = GrammarPrettyPrinter(config: config.printerConfig)
        self.diagramGenerator = GrammarToRailroad()
    }
    
    /// Generates a combined report (Text + Diagram) for the entire grammar.
    public func document(_ syntaxNode: BnfExpression) -> String {
        var output = ""
        
        // Ensure we are working with a list of productions
        let productions: [BnfExpression]
        if case .syntax(let list) = syntaxNode {
            productions = list
        } else {
            productions = [syntaxNode]
        }
        
        // Iterate through productions in original order
        for (index, node) in productions.enumerated() {
            guard case .production(let name, _) = node else { continue }
            
            // Generate Pretty Printed Source
            let sourceText = prettyPrinter.print(node)
            
            // Generate ASCII Diagram
            // Note: We pass the full syntaxNode context so the generator resolves references if needed
            let diagramText = diagramGenerator.generateDiagram(forProduction: name, in: syntaxNode) ?? "(No diagram generated)"
            
            // Assemble the output
            output += sourceText
            output += "\n\n"
            output += diagramText
            
            // Add Spacing/Separator
            if index < productions.count - 1 {
                output += String(repeating: "\n", count: config.verticalSpacing)
                if config.showSeparator {
                    output += String(repeating: String(config.separatorChar), count: config.separatorWidth)
                    output += "\n" + String(repeating: "\n", count: config.verticalSpacing)
                }
            }
        }
        
        return output
    }
}
