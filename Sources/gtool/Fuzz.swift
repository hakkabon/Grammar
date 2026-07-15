//
//  Fuzzer.swift
//  Grammar-Parser
//
//  Created by Ulf Akerstedt-Inoue on 2024/03/20.
//  Copyright © 2024 hakkabon software. All rights reserved.
//

import Foundation
import ArgumentParser
import Grammar

extension GrammarTool {
    
    /// $ gtool fuzz <grammar.bnf> --start <S> [--min <n>] [--max <n>] [--plain]
    /// $ gtool fuzz <grammar.ebnf> --start <S>[--min <n>] [--max <n>] [--plain]
    /// $ gtool fuzz <grammar.gen> [--min <n>] [--max <n>] [--plain]
    /// $ gtool fuzz <grammar.wsn> --start <S> [--min <n>] [--max <n>] [--plain]
    struct Fuzz: ParsableCommand {
        static var configuration = CommandConfiguration(abstract: "Creates sample parse trees from a grammar definition.")

        @OptionGroup var options: Options
      
        @Argument(help: "Minimum number of non-terminals")
        var min: Int = 2
        
        @Argument(help: "Maximum number of non-terminals")
        var max: Int = 5
        
        mutating func run() throws {
            let grammar: Grammar = switch Notation(argument: options.grammar.pathExtension) {
            case .bnf: try Grammar(bnf: try String(contentsOf: options.grammar), start: options.start)
            case .ebnf: try Grammar(ebnf: try String(contentsOf: options.grammar), start: options.start)
            case .gen: try Grammar(gen: try String(contentsOf: options.grammar))
            case .wsn: try Grammar(wsn: try String(contentsOf: options.grammar), start: options.start)
            case .none:
                throw ValidationError("Grammar notation '\(options.grammar.pathExtension)' not recognized.")
            }
            
            print("> \(grammar.start)")
            print("\(grammar)")
            print("")
            
            print("# sample sentence generated from grammar")
            let fuzzer = GrammarFuzzer(grammar: grammar, options: GrammarFuzzer.Options(trace: false))
            let derivation = fuzzer.fuzz(start: grammar.start, conditions: GrammarFuzzer.ExpandConditions(minNonTerminals: min, maxNonTerminals: max))
            print(derivation.leafs.map { "\($0)" }.joined(separator: " "))
            print(derivation)
        }
    }
}
