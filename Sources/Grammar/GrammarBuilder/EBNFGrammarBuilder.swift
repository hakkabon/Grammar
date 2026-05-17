//
//  EBNFGrammarBuilder.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2024/04/21.
//  Copyright © 2024 hakkabon software. All rights reserved.
//

import Foundation

extension Grammar {

    static var ebnfGrammar: Grammar  {
        Grammar(start: "syntax") {
            Rule("syntax") { Seq { n("production") ; n("termination") } }
            Rule("production") {
                n("identifier")
                t("=")
                n("expression")
                n("termination")
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
            Rule("termination") { Alt { t(".") ; t(";") } }
 
            Rule("identifier") { try! rt("[a-zA-Z][_-a-zA-Z0-9]*") }
            Rule("literal") { try! rt("\"[a-zA-Z]*\" | '[a-zA-Z]*'") }
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
