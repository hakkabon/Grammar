//
//  WSNGrammarBuilder.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2024/04/21.
//

import Foundation

extension Grammar {

    /// ```wsn
    /// syntax     = { production } .
    /// production = identifier "=" expression terminator .
    /// expression = term { "|" term } .
    /// term       = factor { factor } .
    /// factor     = identifier
    ///            | literal
    ///            | "[" expression "]"
    ///            | "(" expression ")"
    ///            | "{" expression "}" .
    /// identifier = letter { letter | digit | "-" } .
    /// literal    = """" character { character } """" | "'" character { character } "'" .
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
    /// terminator = ";" | "." .
    ///
    /// ```
    static var wsnGrammar: Grammar {
        Grammar(start: "syntax") {
            Rule("syntax") { Seq { n("production") } }
            Rule("production") {
                n("identifier")
                t("=")
                n("expression")
                n("terminator")
            }
            Rule("expression") { n("term") ; Seq { t("|") ; n("term") } }
            Rule("term") { n("factor") ; Seq { n("factor") } }
            Rule("factor") {
                Alt {
                    n("identifier")
                    n("literal")
                    Opt { n("expression") }
                    Grp { n("expression") }
                    Seq { n("expression") }
                }
            }
            Rule("terminator") { Alt { t(".") ; t(";") } }
 
            Rule("identifier") { try! rt("[a-zA-Z][_-a-zA-Z0-9]*") }
            Rule("literal") { try! rt("\"[^\"]*\"|'[^']*'") }
            Rule("digit") { try! rt("[0-9]") }
            Rule("symbol") {
                Alt {
                t("=")
                t(";") ; t(".")
                t("'") ; t("\"")
                t("|") ; t("{") ; t("}") ; t("[") ; t("]") ; t("(") ; t(")")
                t("-") ; t("*") ; t("+")
                t("ε")
                t("//") ; t("/*") ; t("*/") ; t("(*") ; t("*)")
                }
            }
        }
    }
}
