//
//  GenericGrammar.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/11/19.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

/// A slightly modified version of the WSN (Wirth Syntax Notation) to accomodate
/// BNF gramars as well (by Douglas W. Jones).
///
///```generic
/// syntax      = { metarule | production | comment }
/// metarule    = ( '>' | '/' ) spaces synonym anything
/// production  = nonterminal ( ':' | '=' | ':=' | '::=' ) rhs
/// rhs         = alternative { "|" alternative }
/// alternative = item { item }
/// item        = nonterminal
///             | literal
///             | "[" rhs "]"
///             | "(" rhs ")"
///             | "{" rhs "}"
///
/// nonterminal = '<' identifier '>'
///             | identifier
///
/// identifier  = letter { letter | digit | "-" }
/// literal     = """" character { character } """"
///
/// character   = letter | digit | symbol
/// letter      = [a-zA-Z]
/// digit       = [0-9]
/// symbol      = " " | "!" | "%" | "&" | "(" | ")" | "*" | "+" | "," | "-"
///             | "." | "/" | ":" | ";" | ">" | "=" | "<" | "?" | "@" | "[" | "\" | "]" | "^"
///             | "_" | "`" | "{" | "}" | "~"
///
/// comment     = '#' { anything }
///```
///
/// On a meta level, the WSN grammar uses implicit concatenation, alteration or choice
/// and an iteration construct { ... }, meaning zero or more times, to to define itself.
/// Also, but less important, all non-terminals (IDENTIFIER) are strings, without
/// surrounding single or double apostrophes, all terminals (LITERAL) are
/// quoted strings, every definfinition of a production separates lhs and rhs parts with
/// a "=" symbol, and each definition is terminated with the "." symbol.
///
/// On a practical level,
/// Repetition is denoted by curly brackets, for example
/// ```{a} stands for ε | a | aa | aaa | ...```
/// Optionality is expressed by square brackets, for example
/// ```[a]b stands for ab | b```
/// Parentheses serve for groupings, for example
/// ```(a|b)c stands for ac | bc ```
///
/// Other notation, punctuation and string constructs used.
/// definition          =
/// termination         .
/// terminal string     " ... "
/// terminal string     ' ... '
/// comment             (* ... *)

extension Grammar {

    /// Creates a new grammar from a specification in Douglas W. Jones generic notation.
    ///
    /// - Parameters:
    ///   - string: String describing the grammar in generic notation.
    ///   - start: Start non-terminal
    public init(gen string: String) throws {
        let parser = GrammarParser(grammar: string)
        let syntaxTree: BnfExpression = parser.parse()

        // Convert to Flat Productions
        let converter = StandardNotation()
        let (productions, nonTerminals, start, _, tokens) = converter.rewriteToStandardNotation(syntax: syntaxTree)

        self.init(productions: productions, start: NonTerminal(name: start), lexicalTokens: tokens)
        self.syntaxTree = syntaxTree
        self.generatedNonTerminals = nonTerminals
    }
}
