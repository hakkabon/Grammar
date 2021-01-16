//
//  Production.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2020/05/19.
//

import Foundation

/// A class representing a single production rule written in the form:
///      lhs -> rhs
/// where lhs is a nonterminal symbol.
/// Nonterminals are always a upper case characters, and terminals are written in
/// lower case characters. The rhs is a mix of terminals and nonterminals.

/// This class implements a production rule containing one production symbol
/// (goal symbol) and its corresponding production rule (rhs). Each symbol
/// (terminal and nonterminal) is stored in one string, so each production rule
/// concatenates all of its symbols into one array of symbols.
///
/// Note: There is a distiction between meta terminals like '[]', '{}', '()'
/// used in EBNF to defined the grammar and similar terminals '[]', '{}', '()'
/// used by the user to define his/her grammar. Fortunately, all meta terminals
/// disappear in the process of re-writing the grammar to Standard Form. This is
/// the sole reason why all symbols can be stored as plain strings.
///
/// For example, given the following production rule:
///      E -> E + T | T
/// each symbol is stored as a string and the goal represents the lhs (left to
/// the derivation symbol), and rhs represents everything to the right of the
/// derivation symbol.

public class ProductionRule {
    public var lhs: String
    public var rhs = [String]()
    public var semanticAction = [String]()

    // The priority number of this Production. It is the priority of this Production when
    // resolving parse conflicts. Serves as a means to make each production unique.
    public var priority: Int = 0

    // Used for determining empty derivation.
    var epsilon: Int = 0

    // Indicates if production rule can derive terminals or not.
    var productive = false
    
    public init(lhs: String, rhs: [String]) {
        self.lhs = lhs
        self.rhs = rhs
        self.priority = Grammar.priority.increment()
        self.epsilon = symbolCount
    }
    
    /// Returns number of symbols in the rhs of a production.
    public var symbolCount: Int {
        return !rhs.contains(where: {$0 == Grammar.Constant.eps}) ? rhs.count : rhs.count - 1
    }

    /// Returns true if rhs is empty (epsilon, lambda or blank), otherwise false.
    public var isEmpty: Bool { symbolCount == 0 }
    
    /// Returns true if rhs derives to empty, otherwise false.
    public var derivesEmpty: Bool { epsilon == 0 }
    
    /// Returns true if given symbol is contained in rhs, otherwise false.
    public func containsSymbol(_ symbol: String) -> (Bool,Int) {
        for (i,s) in rhs.enumerated() {
            if s == symbol {
                return (true, i)
            }
        }
        return (false, -1)
    }
    
    /// Returns index of given symbol in rhs if it exists, otherwise -1.
    /// Positions counts from 0,1,... etc.
    public func indexOfSymbol(_ symbol: String) -> Int {
        for (i,s) in rhs.enumerated() {
            if s == symbol {
                return i
            }
        }
        return -1
    }
    
    public func slice(low i1: Int, high i2: Int) -> [String] {
        assert(i1 < i2, "Upper index less than lower: i2 < i1!")
        return Array(rhs[i1...i2])
    }
}

// MARK: Hashable conformance

extension ProductionRule: Hashable {
    public func hash(into hasher: inout Hasher) {
        hasher.combine(lhs)
        hasher.combine(rhs)
    }
}

// MARK: Equatable conformance

public func ==(lhs:ProductionRule, rhs:ProductionRule) -> Bool {
    return lhs.lhs == rhs.lhs && lhs.rhs == rhs.rhs
}

// MARK: Printable conformance

extension ProductionRule: CustomStringConvertible {
    public var description: String {
        let phrase = rhs.joined(separator: " ")
        return "\(lhs) -> \(phrase)"
    }
}
