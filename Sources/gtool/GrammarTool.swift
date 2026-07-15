//
//  BNFParse.swift
//  BNFParser
//
//  Created by Ulf Akerstedt-Inoue on 2024/03/16.
//  Copyright © 2024 hakkabon software. All rights reserved.
//

import Foundation
import ArgumentParser

@main
struct GrammarTool: ParsableCommand {
    
    static var configuration = CommandConfiguration(
        commandName: "gtool",
        abstract: "A driver utility for Grammar. Parsing BNF grammars and fuzzing grammars.",
        version: "0.0.1",
        subcommands: [
            Parse.self,
            Fuzz.self
        ],
        defaultSubcommand: Parse.self
    )

    struct Options: ParsableArguments {

        @Argument(help: "Grammar file name.", transform: URL.init(fileURLWithPath:))
        var grammar: URL
        
        @Option(name: [.short, .long], help: "Start rule of grammmar, except for '.gen' grammars which contain a start declaration.")
        var start: String = ""

        @Option(name: [.short, .long], help: "Choose how to display your grammar - syntax,pretty,railroad.")
        var display: DisplayOptions = [.pretty]

        @Flag(name: .long, help: "Mix pretty print with railroad diagrams.")
        var mix: Bool = false

//TODO: not implemented yet!
//        @Option(name: [.short, .long], help: "Sort grammmar productions alphabetically in ascending or descending order.")
//        var sort: SortOption = .ascend

        mutating func validate() throws {
            // Verify the grammar file actually exists.
            guard FileManager.default.fileExists(atPath: grammar.path) else {
                throw ValidationError("Grammar file does not exist at \(grammar.path)")
            }
            
            // Verify that the grammar has a start rule specified when necessary.
            switch Notation(argument: grammar.pathExtension) {
            case .gen: // start rule is provided inside the grammar file.
                break
            default: // either one of { bnf | ebnf | wsn }
                if start.isEmpty {
                    throw ValidationError("Start rule '\(start)' must be non-empty")
                }
            }
        }
    }
}
