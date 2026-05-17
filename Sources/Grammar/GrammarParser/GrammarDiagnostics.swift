//
//  GrammarDiagnostics.swift
//  BNF-Parser
//
//  Created by Ulf Akerstedt-Inoue on 2020/05/19.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation
import Tokenizer
import TerminalColors

public struct ParserDiagnostic: Error {
    let message: String
    let token: Token
    let location: SourceLocation
}

extension ParserDiagnostic:CustomStringConvertible {
    
    public var description: String {
        return "[\(location.line):\(location.column)] Error: \(message)"
    }
}

struct DiagnosticReporter {
    private let source: String
    private let sourceLines: [String]

    let errorTitle = TerminalColor(fg: .red, .bold, .reversed)
    let brightTitle = TerminalColor(.bold)
    let metaColor = TerminalColor(fg: .blue)
    let squiggleColor = TerminalColor(fg: .red)

    init(source: String) {
        self.source = source
        self.sourceLines = source.components(separatedBy: .newlines)
    }
    
    func report(diagnostics: [ParserDiagnostic]) {
        guard !diagnostics.isEmpty else { return }
        
        let count = diagnostics.count
        print("\n\("Found \(count) \(count > 1 ? "errors:" : "error:")", color: errorTitle)\n")

        for (index, error) in diagnostics.enumerated() {
            print(generateContext(for: error, index: index + 1))
        }
    }
    
    private func generateContext(for error: ParserDiagnostic, index: Int) -> String {
        let lineIndex = error.location.line - 1
        
        guard lineIndex >= 0 && lineIndex < sourceLines.count else {
            return "[\(index)] \(error.description) (Location out of bounds)"
        }
        
        let lineContent = sourceLines[lineIndex]
        
        // Calculate token length using the Token's range
        let range = error.token.range
        let length = source.distance(from: range.lowerBound, to: range.upperBound)
        let tokenLength = max(1, length) // Ensure at least one char is underlined
        
        // Build the visual pointers
        let padding = String(repeating: " ", count: max(0, error.location.column - 1))
        let squiggles = String(repeating: "^", count: tokenLength)
        
        // ANSI Colors: Red (31) for error, Blue (34) for metadata
        let underline = "\(padding)\(squiggles, color: squiggleColor)"
        let gutterNum = "\(String(format: "%3d", error.location.line), color: metaColor) \( "|", color: metaColor) "
        let emptyGutter = "\( "    |", color: metaColor) "
        let arrow = "\( "-->", color: metaColor)"

        // Return the structured multiline string with color encoding.
        return """
        \( "Error #\(index): \(error.message)", color: brightTitle)
           \(arrow) \(error.location.description)
           \(emptyGutter)
           \(gutterNum)\(lineContent)
           \(emptyGutter)\(underline)
        """
    }
}

// MARK: - Diagnostic Types

public struct SourceLocation: CustomStringConvertible {
    let line: Int
    let column: Int
    public var description: String { return "Line \(line):\(column)" }
}

public struct ParserError: Error, CustomStringConvertible {
    let location: SourceLocation
    let message: String
    let context: String
    
    public var description: String {
        return "[\(location)] Error: \(message) (near '\(context)')"
    }
}
