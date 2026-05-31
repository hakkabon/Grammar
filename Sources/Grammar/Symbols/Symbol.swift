//
//  Symbol.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/11/20.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

/// A symbol which can either be a terminal or a non-terminal character
///
/// - terminal: A terminal character
/// - nonTerminal: A non-terminal character
/// - meta: An EBNF character 
public enum Symbol: Codable {
    /// A terminal symbol
    case terminal(Terminal)
    
    /// A non-terminal symbol
    case nonTerminal(NonTerminal)

    /// A meta-terminal symbol
    case metaSymbol(MetaSymbol)
}

extension Symbol: Hashable {
    
    public func hash(into hasher: inout Hasher) {
        switch self {
        case .terminal(let t):
            hasher.combine(t.hashValue)
        case .nonTerminal(let n):
            hasher.combine(n.hashValue)
        case .metaSymbol(let ms):
            hasher.combine(ms.hashValue)
        }
    }
}

extension Symbol: Equatable {

    public static func == (lhs: Symbol, rhs: Symbol) -> Bool {
        switch (lhs, rhs) {
        case (.terminal(let l), .terminal(let r)): return l == r
        case (.nonTerminal(let l), .nonTerminal(let r)): return l == r
        case (.metaSymbol(let l), .metaSymbol(let r)): return l == r
        default:
            return false
        }
    }
}

extension Symbol: CustomStringConvertible {

    public var description: String {
        switch self {
        case .nonTerminal(let n): return n.name
        case .terminal(let t): return t.description
        case .metaSymbol(let ms): return ms.rawValue
        }
    }
}

extension Array<Symbol> {
    
    public var isNullable: Bool {
        if self.count == 0 {
            return true
        } else {
            return self.allSatisfy { symbol in
                switch symbol {
                case .terminal(let t):
                    return t.isEmpty
                case .nonTerminal(_):
                    return false
                case .metaSymbol(_):
                    return false
                }
            }
        }
    }
}

extension Symbol {

    /// Returns `true` if this symbol is a terminal (including meta-terminals).
    public var isTerminal: Bool {
        if case .terminal = self { return true }
        return false
    }

    /// Returns `true` if this symbol is a non-terminal.
    public var isNonTerminal: Bool {
        if case .nonTerminal = self { return true }
        return false
    }

    /// Returns `true` if this symbol represents the empty string (epsilon / lambda).
    /// Matches `.terminal(.meta(.eps))`, `.terminal(.meta(.lambda))`,
    /// `.terminal(.meta(.empty))`, and `.terminal(.string(""))`.
    public var isEpsilon: Bool {
        switch self {
        case .terminal(let t):
            return t.isEmpty
        case .nonTerminal, .metaSymbol:
            return false
        }
    }

    /// Returns the wrapped `NonTerminal` if this symbol is `.nonTerminal`, otherwise `nil`.
    public var nonTerminal: NonTerminal? {
        if case .nonTerminal(let nt) = self { return nt }
        return nil
    }

    /// Returns the wrapped `Terminal` if this symbol is `.terminal`, otherwise `nil`.
    public var terminal: Terminal? {
        if case .terminal(let t) = self { return t }
        return nil
    }
}

extension Array<Symbol> {
    /// Checks if any string in the array starts with the given prefix.
    /// - Parameter prefix: The prefix string to check for.
    /// - Returns: `true` if at least one string in the array has the specified prefix, otherwise `false`.
    func hasPrefix(_ prefix: [Symbol]) -> Bool {
        guard !(prefix.count > self.count) else {
            return false  // A prefix cannot be longer than the main array
        }
        let slicedPrefix = self.prefix(prefix.count)
        return Array(slicedPrefix) == prefix ? true : false
    }

    /// Checks if any string in the array starts with the given prefix.
    /// - Parameter prefix: The prefix string to check for.
    /// - Returns: `true` if at least one string in the array has the specified prefix, otherwise `false`.
    func commonPrefix(with prefix: [Symbol]) -> [Symbol] {
        var common: [Symbol] = []
        let minLength: Int = self.count < prefix.count ? self.count : prefix.count

        for i in 0..<minLength {
            if self[i] == prefix[i] {
                common.append(self[i])
            } else {
                // Mismatch found, stop appending
                break
            }
        }
        return common
    }
}
