//
//  WSNGrammar.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2020/08/22.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

/// ```wsn
/// syntax     = { production } .
/// production = identifier "=" expression "." .
/// expression = term { "|" term } .
/// term       = factor { factor } .
/// factor     = identifier
///            | literal
///            | "[" expression "]"
///            | "(" expression ")"
///            | "{" expression "}" .
/// identifier = letter { letter | digit | "-" } .
/// literal    = """" character { character } """" .
///
/// character  = letter | digit | symbol .
/// letter     = "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M"
///            | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z"
///            | "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m"
///            | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" .
/// digit      = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" .
/// symbol     = "|" | " " | "!" | "#" | "%" | "&" | "(" | ")" | "*" | "+" | "," | "-"
///            | "." | "/" | ":" | ";" | ">" | "=" | "<" | "?" | "@" | "[" | "\" | "]" | "^"
///            | "_" | "`" | "{" | "}" | "~" .
/// ```
///
/// On a meta level, the WSN grammar uses implicit concatenation, alteration or choice
/// and an iteration construct { ... }, meaning zero or more times, to to define itself.
/// Also, but less important, all non-terminals (identifier) are strings, without
/// surrounding single or double apostrophes, all terminals (literal) are
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
///
/// Reference:
/// https://en.wikipedia.org/wiki/Wirth_syntax_notation

extension Grammar {
    
    /// Creates a new grammar from a specification in Wirth Syntax Notation (WSN).
    ///
    /// - Parameters:
    ///   - grammarString: String describing the grammar in WSN
    ///   - start: Start non-terminal
    public init(wsn string: String, start: String) throws {
        let parser = GrammarParser(grammar: string)
        let syntaxTree: BnfExpression = parser.parse()

        // Convert to Flat Productions
        let converter = StandardNotation()
        let (productions, nonTerminals, _, _, tokens) = converter.rewriteToStandardNotation(syntax: syntaxTree)

        self.init(productions: productions, start: NonTerminal(name: start), lexicalTokens: tokens)
        self.syntaxTree = syntaxTree
        self.generatedNonTerminals = nonTerminals
    }
}
