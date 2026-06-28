//
//  GrammarParser.swift
//  BNF-Parser
//
//  Created by Ulf Akerstedt-Inoue on 2019/01/08.
//  Copyright © 2019 hakkabon software. All rights reserved.
//

import Foundation
import OSLog
import Tokenizer

/// A slightly modified version of WSN (Wirth Syntax Notation) to accomodate
/// BNF gramars as well, inspired by the work of Douglas W. Jones.
///
///```
/// syntax      = { metarule | production | comment | lexical }
/// metarule    = ( '>' | '/' ) symbol | synonym
/// synonym     = symbol definition literal                         // synonym
/// production  = nonterminal definition rule [terminator]
/// rule        = term { "|" term }                                 // alternative
/// term        = item { item }                                     // sequence
/// item        = nonterminal                                       // non-quoted string
///             | literal                                           // 'quoted string'
///             | "[" rhs "]"
///             | "(" rhs ")"
///             | "{" rhs "}"
///             | comment
///
/// nonterminal = '<' identifier '>'
///             | identifier
///
/// terminator  = ( '.' | ';' )
/// definition  = ( ':' | '=' | ':=' | '::=' )
///
/// symbol      = " " | "!" | "%" | "&" | "(" | ")" | "*" | "+" | "," | "-"
///             | "." | "/" | ":" | ";" | ">" | "=" | "<" | "?" | "@" | "[" | "\" | "]" | "^"
///             | "_" | "`" | "{" | "}" | "~" | "ε" | "λ"
///
/// comment     = '#' { any-character }                 // one-line comment
///             | "//" { any-character }                // one-line comme
///             | "(*" { any-character } "*)"           // multi-line comment
///             | "/*" { any-character } "*/"           // multi-line comment
///
/// lexical {                                           // opens a lexical scope
///     identifier     = /[a-zA-Z][a-zA-Z0-9-_]*/       // identifier defined by regular expression
///     literal        = /\"[^"]*\"|'[^']*'/            // literal defined by regular expression
///     any-character  = /./                            // any-character defined by regular expression
/// }                                                   // closes a lexical scope
///
/// Lexical elements (type 3 level) can be added in the same file as the CFG definition.
/// These lexical elements must be enclosed by a lexical scope as seen above.
/// Currently avaiable constructs are
/// - regular expressions
/// - range expressions
/// - lists of unicode expressions
///
/// grammar for lexical elements:
///     regex            ::= identifier definition "/" regex-characters "/" [terminator]
///     range-or-list    ::= identifier definition range-type | list-type [terminator]
///     range-type       ::= literal ".." literal [terminator]
///     list-type        ::= literal { "|" literal } [terminator]
///     regex-characters ::= { any-character }
///     
/// examples:
///     lexical {
///         num ::= /\d+(\.\d+)?/ ;
///         cyrillic ::= '\u{0400}' .. '\u{04FF}' ;
///         EMOTICONS ::= '\u{1F600}' | '\u{1F602}' ;
///     }
///```

public class GrammarParser {
    
    // Symbols that are recognized without any enclosing quotation marks.
    let symbols = [
        // comments
        "//",       // single-line comment
        "#",        // single-line comment
        "/*",       // left-multiline-comment
        "*\\",      // right-multiline-comment
        "(*",       // left-multiline-comment
        "*)",       // right-multiline-comment
        
        // empty string
        "ε",        // epsilon (empty string symbol)
        "λ",        // lambda (empty string symbol)
        
        // production definition
        ":",        // definition operator - notational variation
        "=",        // definition operator - EBNF notation
        ":=",       // definition operator - notational variation
        "::=",      // definition operator - BNF notation
        "->",       // definition operator - notational variation
        
        // eol characters
        ".",        // terminator symbol - EBNF notation
        ";",        // terminator symbol - EBNF notation
        
        // sequence character (ebnf only)
        ",",        // comma character - EBNF notation
        
        // BNF / EBNF / WSN specific expression
        "|",        // alternative bar - BNF notation
        "<",        // left anglebracket - BNF notation
        ">",        // right anglebracket - BNF notation
        "{",        // left curly parenthesis - EBNF notation
        "[",        // left bracket - EBNF notation
        "(",        // left parenthesis - EBNF notation
        "}",        // right curly parenthesis - EBNF notation
        "]",        // right bracket - EBNF notation
        ")",        // right parenthesis - EBNF notation
        "?",        // EBNF ? [...] operator
        
        // operators symbols
        "+",        // arithmetic operator - EBNF OneOrMore operator
        "-",        // arithmetic operator - EBNF - subtraction operator
        "*",        // arithmetic operator - EBNF * {...} operator
        "/",        // arithmetic operator
        "^",        // arithmetic operator
        "..",       // range operator
        
        // miscellaneous symbols
        "_" ,
        "`" ,
        "~"
    ]
    
    // synonym sets
    let definingSymbols = Set<String>([":", "=", ":=", "::=", "->"])
    let eolSymbols = Set<String>([".", ";"])
    
    // Keywords that are recognized without any enclosing quotation marks.
    let keywords: [String] = ["lexical", "Lexical", "LEXICAL"] // allow 3 different spellings
    
    private var tokenizer: ParserInput<Tokenizer>
    private var currentToken: Token
    private var source: String
    
    // Accumulate errors using diagnostics.
    public private(set) var diagnostics: [ParserDiagnostic] = []
    private var diagnosticReporter: DiagnosticReporter
    
    // ebnf/wsn or bnf notation?
    public private(set) var isExtended: Bool = false
    
    public init(grammar input: String) {
        self.tokenizer = ParserInput(Tokenizer(input, symbols: Set<String>(symbols), keywords: Set<String>(keywords)))
        self.diagnosticReporter = DiagnosticReporter(source: input)
        self.source = input
        
        // Get first token
        self.currentToken = tokenizer.get()
    }
}

extension GrammarParser {

    /// syntax = { metarule | production | comment | lexical }
    ///
    /// - Returns: complete bnf grammar of type `BnfExpression`.
    public func parse() -> BnfExpression {
        var expressions: [BnfExpression] = []
        
        // Clear stale diagnostics from previous runs
        diagnostics.removeAll()
        
        while currentToken.type != .eof {
            do {
                switch currentToken.type {
                case .symbol(let symbol) where symbol == ">":
                    expressions.append( try parseMetaStartRule() )
                case .symbol(let symbol) where symbol == "<":
                    // Legitimate start of a productions in BNF notation.
                    expressions.append( try parseProduction() )
                case .keyword(let keyword) where keyword.lowercased() == "lexical":
                    let lexicalDefinitions = try parseLexicalDefinitions()
                    lexicalDefinitions.forEach( { expressions.append($0) } )
                case .identifier:
                    // Legitimate start of a productions in EBNF/WSN notation.
                    expressions.append( try parseProduction() )
                case .literal(let literal):
                    throw makeError("a literal \(literal) cannot start a production")
                case .number(let number):
                    throw makeError("malplaced number \(number) in token stream")
                case .comment: advance()
                case .eof:
                    throw makeError("unexpected end of token stream")
                case .invalid(_):
                    throw makeError("invalid token \(currentToken) encountered.")
                default:
                    throw makeError("unexpected token \(currentToken)")
                }
            } catch let error as ParserDiagnostic {
                // Accumulate error
                diagnostics.append(error)
                
                // Synchronize (Panic Mode)
                synchronize()
            } catch {
                // Stop parsing even though not finished.
                print("Unknown error \(error) occurred. Parsing process is terminating ...")
                break
            }
        }
        
        // Report all errors at once after parsing attempts are done
        if !diagnostics.isEmpty {
            diagnosticReporter.report(diagnostics: diagnostics)
        }
        
        return .syntax(expressions)
    }
}

extension GrammarParser {

    /// Discards tokens until it finds a boundary that looks like the start of a new rule
    /// or the clean end of the current one.
    private func synchronize() {
        
        // Consume the token that caused the error to avoid infinite loop
        advance()
        
        while currentToken.type != .eof {
            // We found a semicolon. The next token is likely a fresh start.
            if eolSymbols.contains(currentToken.type.value) {
                return
            }
            
            // Look for the start of a definition.
            // If we see an Identifier followed by ::= or =, we are likely at a new rule.
            // Note: This relies on specific knowledge of EBNF structure.
            
            if case .identifier = currentToken.type {
                // Check if we are parsing the start a production and actually already
                // processing the next production. If we can dectect 'identifier ::=' ahead of current token,
                // we know that a new production will start at the new token.
                if case let .symbol(symbol) = tokenizer.peek(ahead: 1)?.type, definingSymbols.contains(symbol) {
                    Logger.bnf.trace("new production detected: '\(self.currentToken.type)' followed by '\(symbol)'")
                    return
                }
            }
            
            if case .symbol(let symbol) = currentToken.type, symbol == "<" {
                // Check if we are parsing the start of a production and actually already
                // processing the next production. If we can dectect '< identifier > ::=' ahead of current token,
                // we know that a new production will start at the new token.
                if case let .symbol(symbol) = tokenizer.peek(ahead: 3)?.type, definingSymbols.contains(symbol) {
                    Logger.bnf.trace("new production detected: '\(self.currentToken.type)' followed by '\(symbol)'")
                    break
                }
            }
            
            advance()
        }
    }
}

extension GrammarParser {

    /// production = nonterminal definition rule [terminator]
    ///
    /// - Returns: a production of type `BnfExpression`.
    private func parseProduction() throws -> BnfExpression {
        guard case .nonterminal(let nonterminal) = try parseNonterminal() else {
            throw makeError("Expected a production name.")
        }
        
        if !definingSymbols.contains(currentToken.type.value) {
            throw makeError("Expected definition operator '::=' or '=' after '\(nonterminal)'")
        }
        advance()
        
        let expression = try parseRule()
        
        // Allow for an optional line termination - most people are used to this convention.
        // This eol-token is first seen in `parseAlternative` and bubbles up the call hirarchy until it gets here.
        if eolSymbols.contains(currentToken.type.value) { advance() }
        
        return .production(nonterminal, expression)
    }
    
    /// rule = term { "|" term }
    ///
    /// - Returns: a list of choices of type `BnfExpression`.
    private func parseRule() throws -> BnfExpression {
        var terms = [try parseTerm()]
        
        // Collect subsequent alternatives
        while currentToken.type == .symbol("|") {
            advance()
            terms.append(try parseTerm())
        }
        
        // Return term or alternatives of terms.
        return terms.count == 1 ? terms[0] : .alternative(terms)
    }
}

extension GrammarParser {

    /// term = item { item }
    ///
    /// - Returns: a sequence of item of type `BnfExpression`.
    private func parseTerm() throws -> BnfExpression {
        var items = [try parseItem()]
        
        // Loop until we hit a token that CANNOT start an item (like `|`, `)`, `]`, `}`, `;`)
        while isStartOfItem(currentToken.type) {
            
            // Skip EBNF term separator
            if currentToken.type == .symbol(",") { advance() }
            
            if case .identifier = currentToken.type {
                // For EBNF/WSN grammars without terminator symbols.
                // Check if we are parsing off the end of current production and actually already
                // processing the next production. If we can dectect 'identifier ::=' ahead of current token,
                // we know that a new production will start at the new token.
                if case let .symbol(symbol) = tokenizer.peek(ahead: 1)?.type, definingSymbols.contains(symbol) {
                    Logger.bnf.trace("end-of-production detected: '\(self.currentToken.type)' followed by '\(symbol)'")
                    break
                }
            }
            
            if case .symbol(let symbol) = currentToken.type, symbol == "<" {
                // For BNF grammars without terminator symbols.
                // Check if we are parsing off the end of current production and actually already
                // processing the next production. If we can dectect '< identifier > ::=' ahead of current token,
                // we know that a new production will start at the new token.
                if case let .symbol(symbol) = tokenizer.peek(ahead: 3)?.type, definingSymbols.contains(symbol) {
                    Logger.bnf.trace("end-of-production detected: '\(self.currentToken)' followed by '\(symbol)'")
                    break
                }
            }
            
            items.append(try parseItem())
        }
        
        if items.isEmpty {
            throw makeError("Expected an element")
        }
        
        // Return item or sequence of items.
        return items.count == 1 ? items[0] : .sequence(items)
    }
}

extension GrammarParser {

    /// item = nonterminal
    ///      | literal
    ///      | "[" rule "]"
    ///      | "(" rule ")"
    ///      | "{" rule "}"
    ///      | comment
    ///
    /// - Returns: an item of type `BnfExpression`.
    private func parseItem() throws -> BnfExpression {
        switch currentToken.type {
        case .identifier(_):
            return try parseNonterminal()
        case .literal(let val):
            advance()
            return .terminal(val)
        case .number(let number):
            switch number {
            case .decimal(let value), .binary(let value), .octal(let value), .hexadecimal(let value):
                return .terminal("\(value)")
            }
            
            // Tokens that start with a EBNF meta-symbols [...], {...}, and (...)
            
        case .symbol(let symbol) where symbol == "[":
            advance()
            let expr = try parseRule()
            try match(.symbol("]"), "Expected closing ']'")
            return .optional(expr)
        case .symbol(let symbol) where symbol == "{":
            advance()
            let expr = try parseRule()
            try match(.symbol("}"), "Expected closing '}'")
            return .repetition(expr)
        case .symbol(let symbol) where symbol == "(":
            advance()
            let expr = try parseRule()
            try match(.symbol(")"), "Expected closing ')'")
            return .grouping(expr)
            
            // Tokens that start with a certain symbol and implying a special meaning ...
            
        case .symbol(let symbol) where symbol == "<":
            return try parseNonterminal()
            
            // This take care of all other terminals ...
            
        case .symbol(let symbol):
            advance()
            return .terminal(symbol)
            
        default:
            throw makeError("Unexpected token '\(currentToken)'. Expected identifier, string, or grouping.")
        }
    }
}

extension GrammarParser {

    /// nonterminal = '<' identifier '>' | identifier
    ///
    /// - Returns: a nonterminal of type `BnfExpression`.
    private func parseNonterminal() throws -> BnfExpression {
        switch currentToken.type {
        case .symbol(let symbol) where symbol == "<":
            advance()
            if case .identifier(let identifier) = currentToken.type {
                advance()
                // expecting ">" to make it a valid BNF non-terminal
                try match(.symbol(">"), "Expected closing '>' of non-terminal")
                self.isExtended = false
                return .nonterminal(identifier)
            } else {
                throw makeError("expected an identifier in expression")
            }
        case let .identifier(identifier):
            self.isExtended = true
            advance()
            return .nonterminal(identifier)
        default:
            // expected a nonterminal context, but did not receive either '<' nor an identifier, but
            // some crap characters (maybe literals meant to be used for defining regular expressions).
            throw makeError("expected '<' identifier '>' | identifier in expression, not \(currentToken.type).")
        }
    }
}

extension GrammarParser {

    // MARK: - Helpers
    
    private func advance() {
        currentToken = tokenizer.get()
    }

    private func match(_ expected: TokenType, _ message: String) throws {
        if currentToken.type == expected {
            advance()
        } else {
            throw makeError(message)
        }
    }
    
    private func isStartOfItem(_ type: TokenType) -> Bool {
        switch type {
        case .identifier, .literal, .number : return true
        case .symbol("["), .symbol("{"), .symbol("("): return true
        case .symbol("<"): return true
        case .symbol(","): return true
        case .symbol(_):
            return false
        default:
            return false
        }
    }
    
    private func makeError(_ message: String) -> ParserDiagnostic {
        let (line: line, column: column) = currentToken.range.lowerBound.lineAndColumn(in: source)
        let location = SourceLocation(line: line, column: column)
        return ParserDiagnostic(message: message, token: currentToken, location: location)
    }
}

extension GrammarParser {

    /// metarule: '>' '<' identifier '>' | identifier
    ///
    /// - Parameter previous: successfully parsed token that predicts a meta-start context.
    /// - Returns: start rule of grammar.
    private func parseMetaStartRule() throws -> BnfExpression {
        try match(.symbol(">"), "Expected '>' meta symbol")

        guard case .nonterminal(let nonterminal) = try parseNonterminal() else {
            throw makeError("expected '<' identifier '>' | identifier in expression.")
        }
        return .startSymbol(nonterminal)
    }
}

extension GrammarParser {

    /// grammar:
    ///     lexical {
    ///         identifier ::= regex | range-type | list-type
    ///      }
    ///
    /// precondition:
    ///     All definitions must be enclosed by a lexical scope. Each definition must be
    ///     terminated with new line or terminator character.
    ///
    /// - Returns: a list of type 3 level expressions of type `BnfExpression`.
    private func parseLexicalDefinitions() throws -> [BnfExpression] {
        var lexicalDefinitions: [BnfExpression] = []

        advance() // allow "lexical" keyword with different spelling
        try match(.symbol("{"), "Expected '{' got something else")
        
        while currentToken.type != .symbol("}") {
            switch currentToken.type {

            case .identifier(let identifier):
                lexicalDefinitions.append(try parseLexicalDefinition(for: identifier))

            case .literal(let name):
                throw makeError("Expected indentifier found '\(name)'")
                
            default:
                throw makeError("Unexpected token '\(currentToken)'")
            }
        }
        try match(.symbol("}"), "Expected '}' got \(currentToken)")
        return lexicalDefinitions
    }
    
    /// grammar:
    ///     regex            ::= identifier definition "/" regex-characters "/" [terminator]
    ///     range-or-list    ::= identifier definition range-type | list-type [terminator]
    ///     range-type       ::= literal ".." literal [terminator]
    ///     list-type        ::= literal { "|" literal } [terminator]
    ///     regex-characters ::= { any-character }
    ///
    /// precondition:
    ///     All definitions must be enclosed by a lexical scope. Each definition must be
    ///     terminated with new line or terminator character.
    ///
    /// - Returns: a type 3 level expression of type `BnfExpression`.
    private func parseLexicalDefinition(for identifier: String) throws -> BnfExpression {
        advance()

        if !definingSymbols.contains(currentToken.type.value) {
            throw makeError("Expected definition operator ':', '=' or '::=' after '\(identifier)'")
        }
        advance()
        
        switch currentToken.type {
        case .regex(let regex):
            advance()

            // Allow for an optional line termination - most people are used to this convention.
            if eolSymbols.contains(currentToken.type.value) { advance() }

            return .regex(identifier,regex)
            
        case .literal(let literal):
            advance()

            if case let .symbol(symbol) = currentToken.type, symbol == ".." {
                advance()
                guard case .literal(let upperBound) = currentToken.type else {
                    throw makeError("Expected upper bound in range definition.")
                }
                advance()
                // Allow for an optional line termination - most people are used to this convention.
                if eolSymbols.contains(currentToken.type.value) { advance() }

                return .range(identifier, literal, upperBound)
                
            } else {
                return try parseListDefinition(for: identifier, firstElement: literal)
            }
        
        default:
            throw makeError("Expected name of lexical identifier.")
        }
    }
    
    func parseListDefinition(for identifier: String, firstElement: String) throws -> BnfExpression {
        var elements: [String] = [firstElement]

        while case let .symbol(symbol) = currentToken.type, symbol == "|" {
            advance()
            guard case .literal(let element) = currentToken.type else {
                throw makeError("Expected another element in list definition.")
            }
            elements.append(element)
            advance()
        }
        // Allow for an optional line termination - most people are used to this convention.
        if eolSymbols.contains(currentToken.type.value) { advance() }

        return .list(identifier, elements)
    }
}
