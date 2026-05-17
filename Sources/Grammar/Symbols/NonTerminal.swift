//
//  NonTerminal.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/11/20.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

/// A non-terminal symbol, which cannot occur in a word recognized by a parser
public struct NonTerminal: Codable {
    
    /// Name of the non-terminal
    public let name: String
            
    /// Creates a new non-terminal symbol with a given name
    ///
    /// - Parameter name: Name of the non-terminal symbol
    public init(name: String) {
        self.name = name
    }
}

extension NonTerminal: Equatable {
    public static func == (lhs: NonTerminal, rhs: NonTerminal) -> Bool {
        return lhs.name == rhs.name
    }
}

extension NonTerminal: Comparable {
    public static func < (lhs: NonTerminal, rhs: NonTerminal) -> Bool {
        return lhs.name < rhs.name
    }
}

extension NonTerminal: Hashable {
    public func hash(into hasher: inout Hasher) {
        hasher.combine(name.hashValue)
    }
}

extension NonTerminal: CustomStringConvertible {
    public var description: String {
        return name
    }
}

extension NonTerminal: ExpressibleByStringLiteral {
    public typealias StringLiteralType = String
    
    public init(stringLiteral value: String) {
        self.init(name: value)
    }
}
