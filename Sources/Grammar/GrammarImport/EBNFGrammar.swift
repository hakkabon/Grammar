//
//  EBNFGrammar.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2020/08/22.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

///```ebnf
/// grammar       = ( rule ) * ;
///
/// rule          = lhs "=" rhs terminator ;
///
/// lhs           = identifier ;
/// rhs           = alternation ;
///
/// alternation   = concatenation { "|" concatenation } ;
/// concatenation = factor { factor } ;
///
/// factor        = term "?"
///               | term "*"
///               | term "+"
///               | term "-" term
///               | term
///               ;
///
/// term          = identifier
///               | terminal
///               | "[" rhs "]"
///               | "(" rhs ")"
///               | "{" rhs "}"
///               ;
///
/// terminator    = ";" | "." ;
///
/// terminal      = "'" , character - "'" , { character - "'" } , "'"
///               | '"' , character - '"' , { character - '"' } , '"' ;
///
/// S = { " " | "\n" | "\t" | "\r" | "\f" | "\b" } ;
///
/// identifier = letter , { letter | digit | "_" } ;
/// character = letter | digit | symbol | "_" | " " ;
///
/// symbol = "[" | "]" | "{" | "}" | "(" | ")" | "<" | ">"
///        | "'" | '"' | "=" | "|" | "." | "," | ";" | "-"
///        | "+" | "*" | "?" | "\n" | "\t" | "\r" | "\f" | "\b" ;
///
/// digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
///
/// letter = "A" | "B" | "C" | "D" | "E" | "F" | "G"
///        | "H" | "I" | "J" | "K" | "L" | "M" | "N"
///        | "O" | "P" | "Q" | "R" | "S" | "T" | "U"
///        | "V" | "W" | "X" | "Y" | "Z" | "a" | "b"
///        | "c" | "d" | "e" | "f" | "g" | "h" | "i"
///        | "j" | "k" | "l" | "m" | "n" | "o" | "p"
///        | "q" | "r" | "s" | "t" | "u" | "v" | "w"
///        | "x" | "y" | "z" ;
///```
/// On a meta level, the EBNF grammar does not use concatenation, but the comma operator to concatenate
/// symbols, and the following constructs to to define itself.
/// concatenation       ,
/// alternation         |
/// optional            [ ... ]
/// repetition          { ... }
/// grouping            ( ... )
/// optional            ?           postfix operator
/// zero or more        *           postfix operator
/// one or more         +           postfix operator
/// exception           -           prefix operator
///
/// EBNF uses conventions such as "-" to indicate set disjunction, "+" to indicate one or more matches,
/// and "?" for optionality)
///
/// Other notation, punctuation and string constructs used.
/// definition          =
/// termination         ;
/// terminal string     " ... "
/// terminal string     ' ... '
/// comment             (* ... *)
/// special sequence    ? ... ?
///
/// Reference:
/// ISO/IEC 14977

extension Grammar {

    /// Creates a new grammar from a specification in Extended Backus-Naur Form (EBNF)
    /// notation.
    ///
    /// - Parameters:
    ///   - string: String describing the grammar in EBNF notation
    ///   - start: Start non-terminal
    public init(ebnf string: String, start: String) throws {
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
