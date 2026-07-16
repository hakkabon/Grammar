//
//  BNFGrammarBuilder.swift.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2024/04/21.
//  Copyright © 2024 hakkabon software. All rights reserved.
//

import Foundation

extension Grammar {
    
    /// The essence of BNF
    ///
    ///```bnf
    /// <syntax>         ::= <rule> | <rule> <syntax>
    /// <rule>           ::= "<" <rule-name> ">" "::=" <expression> <line-end>
    /// <expression>     ::= <list> | <list> "|" <expression>
    /// <list>           ::= <term> | <term> <list>
    /// <term>           ::= <literal> | "<" <rule-name> ">"
    /// <literal>        ::= '"' <character> '"' | "'" <character> "'"
    ///
    /// <character>      ::= <letter> | <digit> | <symbol>
    /// <rule-name>      ::= <letter> | <rule-name> <rule-char>
    /// <rule-char>      ::= <letter> | <digit> | "-"
    /// <line-end>       ::= <eol> | <eol> <line-end>
    /// <letter>         ::= "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" |
    ///                      "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z" |
    ///                      "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" |
    ///                      "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z"
    /// <digit>          ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
    /// <symbol>         ::= "|" | " " | "!" | "#" | "$" | "%" | "&" | "(" | ")" | "*" | "+" | "," | "-" |
    ///                      "." | "/" | ":" | ";" | ">" | "=" | "<" | "?" | "@" | "[" | "\" | "]" | "^" |
    ///                      "_" | "`" | "{" | "}" | "~"
    /// <eol>            ::= "\n" | "\r\n"
    ///```
    static var bnfGrammar: Grammar  {
        Grammar(start: "syntax") {

            Rule("syntax") { Alt { n("rule") ; Cat { n("rule") ; n("syntax") } } }
            
            Rule("rule") { t("<") ; n("rule-name") ; t(">") ; t("::=") ; n("expression") ; n("line-end") }
            
            Rule("expression") { Alt { n("list") ; Cat { t("|") ; n("expression") } } }
            
            Rule("list") { Alt { n("term") ; Cat { n("term") ; n("list") } } }
            
            Rule("term") { Alt { n("literal") ; Cat { t("<") ; n("rule-name") ; t(">") } } }
            
            Rule("literal") { Alt { Cat { t("\"") ; n("character") ; t("\"") } ; Cat { t("'") ; n("character") ; t("'") } } }
            
            Rule("character") { Alt { n("letter") ; n("digit") ; n("symbol") } }
            
            Rule("rule-name") { Alt { n("letter") ; Cat { n("rule-name") ; n("rule-char") } } }
            
            Rule("rule-char") { Alt { n("letter") ; n("digit") ; t("-") } }
            
            Rule("line-end") { Alt { n("eol") ; Cat { n("eol") ; n("line-end") } } }
            
            Rule("symbol") {
                Alt {
                    t("|") ; t(" ") ; t("!") ; t("#") ; t("$") ; t("%") ; t("&") ; t("(") ;
                    t(")") ; t("*") ; t("+") ; t(",") ; t("-") ; t(".") ; t("/") ; t(":") ;
                    t(";") ; t(">") ; t("=") ; t("<") ; t("?") ; t("@") ; t("[") ; t("\\") ;
                    t("]") ; t("^") ; t("_") ; t("`") ; t("{") ; t("}") ; t("~")
                }
            }

            Rule("letter") { try! rt("\"[a-zA-Z]\"") }

            Rule("digit") { try! rt("[0-9]") }

            Rule("eol") { Alt { t("\n") ; t("\r") ; t("\r\n") } }
        }
    }
    
    ///```bnf
    /// <syntax>         ::= <rule> | <rule> <syntax>
    /// <rule>           ::= "<" <rule-name> ">" "::=" <expression> <line-end>
    /// <expression>     ::= <list> | <list> "|" <expression>
    /// <list>           ::= <term> | <term> <list>
    /// <term>           ::= <literal> | "<" <rule-name> ">"
    /// <literal>        ::= '"' <text1> '"' | "'" <text2> "'"
    /// <text1>          ::= "" | <character1> <text1>
    /// <text2>          ::= "" | <character2> <text2>
    /// <character>      ::= <letter> | <digit> | <symbol>
    /// <letter>         ::= "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" | 
    ///                      "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z" |
    ///                      "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" |
    ///                      "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z"
    /// <digit>          ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
    /// <symbol>         ::= "|" | " " | "!" | "#" | "$" | "%" | "&" | "(" | ")" | "*" | "+" | "," | "-" | 
    ///                      "." | "/" | ":" | ";" | ">" | "=" | "<" | "?" | "@" | "[" | "\" | "]" | "^" |
    ///                      "_" | "`" | "{" | "}" | "~"
    /// <character1>     ::= <character> | "'"
    /// <character2>     ::= <character> | '"'
    /// <rule-name>      ::= <letter> | <rule-name> <rule-char>
    /// <rule-char>      ::= <letter> | <digit> | "-"
    /// <line-end>       ::= <eol> | <eol> <line-end>
    /// <eol>            ::= "\n" | "\r\n"
    ///```
    static var bnf2Grammar: Grammar  {
        Grammar(start: "syntax") {
            Rule("syntax") {
                Alt {
                    n("rule")
                    Cat {
                        n("rule")
                        n("syntax")
                    }
                }
            }
            Rule("rule") {
                t("<")
                n("rule-name")
                t(">")
                t("::=")
                n("expression")
                n("line-end")
            }
            Rule("expression") {
                Alt {
                    n("list")
                    Cat {
                        t("|")
                        n("expression")
                    }
                }
            }
            Rule("line-end") { 
                Alt {
                    n("eol")
                    Cat {
                        n("eol")
                        n("line-end")
                    }
                }
            }
            Rule("list") {
                Alt {
                    n("term")
                    Cat {
                        n("term")
                        n("list")
                    }
                }
            }
            Rule("term") {
                Alt {
                    n("literal")
                    Cat {
                        t("<")
                        n("rule-name")
                        t(">")
                    }
                }
            }
            Rule("literal") {
                Alt {
                    Cat {
                        t("\"")
                        n("text1")
                        t("\"")
                    }
                    Cat {
                        t("'")
                        n("text2")
                        t("'")
                    }
                }
            }
            Rule("rule-name") {
                Alt {
                    n("letter")
                    Cat {
                        n("rule-name")
                        n("rule-char")
                    }
                }
            }
            Rule("rule-char") {
                Alt {
                    n("letter")
                    n("digit")
                    t("-")
                }
            }
            Rule("text1") {
                Alt {
                    t("")
                    Cat {
                        n("character1")
                        n("text1")
                    }
                }
            }
            Rule("text2") {
                Alt {
                    t("")
                    Cat {
                        n("character2")
                        n("text1")
                    }
                }
            }
            Rule("character") {
                Alt {
                    n("letter")
                    n("digit")
                    n("symbol")
                }
            }
            Rule("symbol") {
                Alt {
                    t("|") ; t(" ") ; t("!") ; t("#") ; t("$") ; t("%") ; t("&") ; t("(") ;
                    t(")") ; t("*") ; t("+") ; t(",") ; t("-") ; t(".") ; t("/") ; t(":") ;
                    t(";") ; t(">") ; t("=") ; t("<") ; t("?") ; t("@") ; t("[") ; t("\\") ;
                    t("]") ; t("^") ; t("_") ; t("`") ; t("{") ; t("}") ; t("~")
                }
            }
            Rule("character1") {
                Alt {
                    n("character")
                    t("'")
                }
            }
            Rule("character2") {
                Alt {
                    n("character")
                    t("\"")
                }
            }
            Rule("letter") { try! rt("\"[a-zA-Z]\"") }
            Rule("digit") { try! rt("[0-9]") }
            Rule("EOL") { 
                Alt {
                    t("\n")
                    t("\r")
                    t("\r\n")
                }
            }
        }
    }
}
