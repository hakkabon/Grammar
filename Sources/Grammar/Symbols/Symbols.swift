//
//  Symbols.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/11/20.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

/// Creates a new terminal symbol
///
/// - Parameter value: Value of the terminal symbol
/// - Returns: A terminal symbol with the given value
public func t(_ value: String) -> Symbol {
    return Symbol.terminal(Terminal(string: value))
}

/// Creates a new non-terminal symbol
///
/// - Parameter name: Name of the non-terminal symbol
/// - Returns: A non-terminal symbol with the given name
public func n(_ name: String) -> Symbol {
    return Symbol.nonTerminal(NonTerminal(name: name))
}

/// Creates a new regular terminal symbol
///
/// - Parameter value: Regular value of the terminal
/// - Returns: A regular terminal symbol
/// - Throws: An error indicating that the given regular expression is invalid
public func rt(_ value: String) throws -> Symbol {
    return try Symbol.terminal(Terminal(expression: value))
}

/// Creates a new character-range terminal symbol, matched when the tokenized
/// subsequence is a single character falling inside `range`.
///
/// - Parameter range: Inclusive range of matched characters, e.g. `"0" ... "9"`
/// - Returns: A range terminal symbol
public func ct(_ range: ClosedRange<Character>) -> Symbol {
    return Symbol.terminal(Terminal(range: range))
}

/// Creates a new list terminal symbol, matched when the tokenized subsequence
/// is equal to one of the given literal alternatives.
///
/// - Parameter values: Literal alternatives, e.g. `lt("true", "false")`
/// - Returns: A list terminal symbol
public func lt(_ values: String...) -> Symbol {
    return Symbol.terminal(Terminal(list: values))
}

/// Creates a new meta-terminal symbol
///
/// - Parameter name: Name of the meta-terminal symbol
/// - Returns: A meta-terminal symbol with the given name
public func mt(_ name: String) -> Symbol {
    return .terminal(.meta(MetaTerminal(rawValue: name) ?? MetaTerminal.eps))
}

/// Creates a new meta-symbol symbol
///
/// - Parameter name: Name of the meta-terminal symbol
/// - Returns: A meta-terminal symbol with the given name
public func ms(_ name: String) -> Symbol {
    return Symbol.metaSymbol(MetaSymbol(rawValue: name) ?? MetaSymbol.lbrace)
}
