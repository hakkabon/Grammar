//
//  SymbolSet.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/11/20.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

/// A set of terminal or non-terminal symbols
public struct SymbolSet {
    
    /// Whitespace characters (space, tab and line break)
    public static let whitespace = SymbolSet(" \t\n".map(String.init).map(t))
    
    /// Lower case letters a to z
    public static let lowercase = SymbolSet("abcdefghijklmnopqrstuvwxyz".map(String.init).map(t))
    
    /// Upper case letters A to Z
    public static let uppercase = SymbolSet("ABCDEFGHIJKLMNOPQRSTUVWXYZ".map(String.init).map(t))
    
    /// Decimal digits 0 to 9
    public static let numbers = SymbolSet((0...9).map(String.init).map(t))
    
    /// Lower and upper case letters a to z and A to Z
    public static var letters: SymbolSet {
        return SymbolSet((lowercase.symbols + uppercase.symbols).map { $0 })
    }
    
    /// Alphanumeric characters (Letters and numbers)
    public static var alphanumerics: SymbolSet {
        return SymbolSet((letters.symbols + numbers.symbols).map { $0 })
    }
    
    /// Symbols contained in this symbol set
    public let symbols: [Symbol]
    
    /// Creates a new symbol set given a sequence of symbols
    ///
    /// - Parameter sequence: Sequence of symbols which the symbol set should contain
    public init<S: Sequence>(_ sequence: S) where S.Element == Symbol {
        self.symbols = Array(sequence)
    }
}
