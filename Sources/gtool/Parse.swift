//
//  Standard.swift
//  BnfParse
//
//  Created by Ulf Akerstedt-Inoue on 2024/03/16.
//  Copyright © 2024 hakkabon software. All rights reserved.
//

import Foundation
import ArgumentParser
import Grammar

extension GrammarTool {
    
    /// Traditional hand-coded parser for BNF.
    /// The BNF notation used may vary according to the given file extension { bnf | ebnf | gen | wsn }.
    ///
    /// $ gtool [bnf] <grammar.bnf> --start <S> [--display syntax,pretty,railroad] [--mix]
    /// $ gtool [bnf] <grammar.ebnf> --start <S> [--display syntax,pretty,railroad] [--mix]
    /// $ gtool [bnf] <grammar.gen> [--display syntax,pretty,railroad] [--mix]
    /// $ gtool [bnf] <grammar.wsn> --start <S> [--display syntax,pretty,railroad] [--mix]
    struct Parse: ParsableCommand {

        static var configuration = CommandConfiguration(abstract: "Parses BNF grammars using traditional hand-coded parser.")

        @OptionGroup var options: Options

        mutating func run() throws {
            var config = GrammarPrettyPrinter.Configuration()
            config.definitionOperator = "::="
            config.terminator = ";"
            config.indentWidth = 4

            let inputString = try String(contentsOf: options.grammar)
            let parser = switch Notation(argument: options.grammar.pathExtension) {
            case .bnf, .ebnf, .gen, .wsn:
                GrammarParser(grammar: inputString)
            case .none:
                throw ValidationError("Grammar notation '\(options.grammar.pathExtension)' not recognized.")
            }
            
            let syntaxTree: BnfExpression = parser.parse()
            if parser.diagnostics.isEmpty {
                print("\nParse successful.\n")
                
                if options.display.contains(.syntax) {
                    print(syntaxTree)
                }

                if options.mix {
                    var docConfig = GrammarDocumenter.Configuration()
                    docConfig.separatorChar = "="
                    docConfig.printerConfig.definitionOperator = "::="
                    docConfig.printerConfig.indentWidth = 4
                    let documenter = GrammarDocumenter(config: docConfig)

                    // Generate Output
                    let report = documenter.document(syntaxTree)
                    print(report)
                } else {
                    if options.display.contains(.pretty) {
                        let printer = GrammarPrettyPrinter(config: config)
                        let prettySource = printer.print(syntaxTree)
                        print(prettySource + "\n")
                    }
                    
                    if options.display.contains(.railroad) {
                        let diagramGen = GrammarToRailroad()
                        let output = diagramGen.generateDiagrams(syntaxTree)
                        print(output)
                    }
                }
            } else {
                print("\nPlease correct your bnf grammar\n")
            }
        }
    }
}
