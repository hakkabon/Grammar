//
//  BNFGrammar.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2020/08/22.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

///```bnf
/// <syntax>         ::= <rule> | <rule> <syntax>
/// <rule>           ::= "<" <rule-name> ">" "::=" <expression> <line-end>
/// <expression>     ::= <list> | "|" <expression>
/// <line-end>       ::= <eol> | <eol> <line-end>
/// <list>           ::= <term> | <term> <list>
/// <term>           ::= <literal> | "<" <rule-name> ">"
/// <literal>        ::= '"' <text1> '"' | "'" <text2> "'"
/// <text1>          ::= "" | <character1> <text1>
/// <text2>          ::= "" | <character2> <text2>
/// <character>      ::= <letter> | <digit> | <symbol>
/// <letter>         ::= "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M"
///                  | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z"
///                  | "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m"
///                  | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z"
/// <digit>          ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
/// <symbol>         ::= "|" | " " | "!" | "#" | "$" | "%" | "&" | "(" | ")" | "*" | "+" | "," | "-"
///                  | "." | "/" | ":" | ";" | ">" | "=" | "<" | "?" | "@" | "[" | "\" | "]" | "^"
///                  | "_" | "`" | "{" | "}" | "~"
/// <character1>     ::= <character> | "'"
/// <character2>     ::= <character> | '"'
/// <rule-name>      ::= <letter> | <rule-name> <rule-char>
/// <rule-char>      ::= <letter> | <digit> | "-"
/// <eol>            ::= "\n" | "\r\n"
///```
///
/// On a meta level, the BNF grammar uses implicit concatenation, alteration or choice
/// to to define itself.
/// Also, but less important, all non-terminals (rule-name) are strings, with
/// surrounding angular brackets "<" ">", all terminals (literal) are
/// quoted strings, every definfinition of a production separates lhs and rhs parts with
/// a "::=" symbol, and each definition is terminated with a line-end (EOL).
///
/// Reference:
/// https://en.wikipedia.org/wiki/Backus–Naur_form

extension Grammar {

    /// Creates a new grammar from a specification in Backus-Naur Form (BNF)
    /// notation.
    ///
    /// - Parameters:
    ///   - string: String describing the grammar in BNF notation
    ///   - start: Start non-terminal
    public init(bnf string: String, start: String) throws {
        let parser = GrammarParser(grammar: string)
        let syntaxTree: BnfExpression = parser.parse()

        // Convert to Flat Productions
        let converter = StandardNotation()
        let (productions, nonTerminals, _, _, tokens) = converter.rewriteToStandardNotation(syntax: syntaxTree)
        // define all terminals with their corresponding lexical definitions
        
        self.init(productions: productions, start: NonTerminal(name: start), lexicalTokens: tokens)
        self.syntaxTree = syntaxTree
        self.generatedNonTerminals = nonTerminals
    }
}
