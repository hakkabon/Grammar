//
//  Vocabulary.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2026/07/06.
//  Copyright © 2026 hakkabon software. All rights reserved.
//

import Foundation

/// The Grammar Vocabulary
/// Instead of just returning strings, the protocol should return dictionaries mapping
/// the string/pattern to the expected TokenType, and separate exact matches from regex
/// matches.

public protocol GrammarVocabulary {
    /// Exact word matches (e.g., "if", "while", "return", "class")
    var keywords: [String: AnyHashable] { get }
    
    /// Exact symbol matches (e.g., "+", "==", "->", "{")
    var symbols: [String: AnyHashable] { get }
    
    /// Regex pattern matches (e.g., "[a-zA-Z_][a-zA-Z0-9_]*" for Identifiers)
    var patterns: [String: AnyHashable] { get }
    
    /// Token types that should be lexed but hidden from the parser (whitespace, comments)
    var skippedTypes: Set<AnyHashable> { get }
}

// Provide a default implementation so grammars only implement what they need
public extension GrammarVocabulary {
    var keywords: [String: AnyHashable] { [:] }
    var symbols: [String: AnyHashable] { [:] }
    var patterns: [String: AnyHashable] { [:] }
    var skippedTypes: Set<AnyHashable> { [] }
}
