//
//  Production.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/06.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation

/// A class representing a single production rule written in the form:
///      lhs -> rhs
/// where lhs is a non-terminal symbol and the rhs is alist of non-terminals and
/// terminals.
/// This class implements a production rule containing one production symbol
/// (goal symbol) and its corresponding production rule (rhs). Each symbol
/// (terminal and non-terminal) is stored in one string, so each production rule
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
///
/// ## Epsilon (empty) productions
///
/// A production that derives the empty string is represented internally as
/// `rule == []`, never as a rule containing an explicit epsilon symbol such as
/// `.terminal(.meta(.eps))`. This is enforced at creation: every initializer
/// below normalizes its `rule` argument by dropping any symbol for which
/// `Symbol.isEpsilon` is `true` (epsilon is the identity element of
/// concatenation, so removing it anywhere in a rule never changes the language
/// generated). The practical effect is that callers may freely write
/// `Production(goal: N, rule: [.terminal(.meta(.eps))])` and receive back a
/// `Production` whose `rule` is `[]` — there is exactly one canonical
/// representation of "this non-terminal can derive nothing", which keeps
/// `rule.isEmpty` a reliable test everywhere in the package (`isNullable`,
/// `Hygiene.eliminateEmpty`, the CNF/GNF converters, the Earley/RNGLR
/// pipelines, etc.).
///
/// The epsilon *meta character* itself ('ε', 'λ', or whatever a grammar's
/// `Grammar.epsilon` is set to) is purely a rendering concern: it is produced
/// on demand by `description` and by `Grammar.bnf`/`ebnf`/`wsn` when a
/// production's `rule` is empty, but it is never part of the stored data.
public struct Production: Codable {
    
    /// Starting pattern
    public let goal: NonTerminal
    
    /// Symbols produced by substitution from the goal non terminal.
    ///
    /// An empty array (`[]`) is the sole, canonical representation of an
    /// epsilon/empty production. See the type-level documentation above.
    public let rule: [Symbol]
    
    /// Creates a new production.
    ///
    /// The given `rule` is normalized before being stored: any symbol that
    /// `isEpsilon` (e.g. `.terminal(.meta(.eps))`, `.terminal(.meta(.lambda))`,
    /// or `.terminal(.string(""))`) is dropped, so a rule that denotes nothing
    /// but the empty string collapses to `[]`.
    ///
    /// - Parameters:
    ///   - goal: Starting pattern
    ///   - rule: Generated sequence of symbols
    public init(goal: NonTerminal, rule: [Symbol]) {
        self.goal = goal
        self.rule = Production.normalize(rule)
    }
    
    /// Creates a new production.
    ///
    /// The given `rule` is normalized exactly as in `init(goal:rule:)`.
    ///
    /// - Parameters:
    ///   - goal: Starting pattern
    ///   - rule: Generated sequence of symbols
    ///   - chain: Non-terminals which have been filtered out during normalization
    public init(goal: NonTerminal, rule: [Symbol], chain: [NonTerminal]? = nil) {
        self.goal = goal
        self.rule = Production.normalize(rule)
    }

    /// Removes every epsilon-equivalent symbol from `rule`. Epsilon is the
    /// identity element under concatenation, so dropping it — wherever it
    /// occurs — never changes the string the rule derives. A rule consisting
    /// solely of epsilon symbols therefore becomes `[]`, the canonical
    /// representation of an empty production.
    static func normalize(_ rule: [Symbol]) -> [Symbol] {
        guard rule.contains(where: { $0.isEpsilon }) else { return rule }
        return rule.filter { !$0.isEpsilon }
    }
}

extension Production {

    private enum CodingKeys: String, CodingKey {
        case goal, rule
    }

    /// Decodes a production and normalizes its `rule`, exactly as every other
    /// initializer does. Without this, decoding previously-serialized data
    /// containing a legacy `[.terminal(.meta(.eps))]`-style rule would bypass
    /// normalization entirely, since the compiler-synthesized `Decodable`
    /// conformance assigns directly to stored properties.
    public init(from decoder: Decoder) throws {
        let container = try decoder.container(keyedBy: CodingKeys.self)
        self.goal = try container.decode(NonTerminal.self, forKey: .goal)
        self.rule = Production.normalize(try container.decode([Symbol].self, forKey: .rule))
    }

    public func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)
        try container.encode(goal, forKey: .goal)
        try container.encode(rule, forKey: .rule)
    }
}

extension Production: Hashable {
    
    public func hash(into hasher: inout Hasher) {
        hasher.combine(goal)
        hasher.combine(rule)
    }
}

extension Production: Equatable {
    
    public static func == (lhs: Production, rhs: Production) -> Bool {
        return lhs.goal == rhs.goal && lhs.rule == rhs.rule
    }
}

extension Production: Comparable {

    public static func < (lhs: Production, rhs: Production) -> Bool {
        // First compare by goal symbol
        if lhs.goal != rhs.goal {
            return lhs.goal < rhs.goal
        }
        // Then compare by symbol length of rhs
        return lhs.rule.count < rhs.rule.count
    }
}

extension Production {

    init(goal: NonTerminal, @ProductionBuilder builder: () -> ProductionResult) {
        self.goal = goal

        switch builder() {
        case let .con(symbols):
            self.rule = Production.normalize(symbols)
        case let .alt(symbols):
            self.rule = Production.normalize(symbols.flatMap { $0 })
        }
    }
}

extension Production {

    /// A production is final if it only generates terminal symbols
    public var isFinal: Bool {
        return self.rule.allSatisfy { symbol -> Bool in
            if case .terminal(_) = symbol {
                return true
            } else {
                return false
            }
        }
    }
    
    /// A production is in Chomsky normal form if it generates exactly 2 non-terminals
    /// exclusive or one or zero terminal symbols
    public var isInChomskyNormalForm: Bool {
        if isFinal {
            return rule.count == 1
        }
        return self.rule.allSatisfy { symbol -> Bool in
            if case .nonTerminal(_) = symbol {
                return true
            } else {
                return false
            }
        } && self.rule.count == 2
    }
    
    public var isNullable: Bool {
        return rule.allSatisfy { symbol in
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
    
    /// Sequence of terminals generated by this production
    public var generatedTerminals: [Terminal] {
        return rule.compactMap { symbol -> Terminal? in
            guard case .terminal(let terminal) = symbol  else {
                return nil
            }
            return terminal
        }
    }
    
    /// Sequence of non-terminals generated by this production
    public var generatedNonTerminals: [NonTerminal] {
        return rule.compactMap { symbol -> NonTerminal? in
            guard case .nonTerminal(let nonTerminal) = symbol else {
                return nil
            }
            return nonTerminal
        }
    }

    /// Returns true if given symbol is contained in rhs, otherwise false.
    public func containsSymbol(_ symbol: Symbol) -> (match: Bool, position: Int)? {
        for (i,s) in rule.enumerated() {
            if s == symbol {
                return (match: true, position: i)
            }
        }
        return nil
    }
}

extension Production: CustomStringConvertible {

    /// A human-readable rendering of the production, e.g. `"E --> E + T"`.
    ///
    /// `Production` itself has no notion of which epsilon meta character a
    /// particular `Grammar` has chosen to display (see `Grammar.epsilon`), so
    /// an empty rule is rendered using the package default, `MetaTerminal.eps`
    /// ("ε"). Call sites that have access to a `Grammar` and want its
    /// configured character instead (e.g. "λ") should use `Grammar.bnf`,
    /// `Grammar.ebnf`, or `Grammar.wsn`.
    public var description: String {
        guard !rule.isEmpty else {
            return "\(goal.name) --> \(MetaTerminal.eps.description)"
        }
        return "\(goal.name) --> \(rule.map { $0.description }.joined(separator: " ") )"
    }
}

extension Production: CustomDebugStringConvertible {

    public var debugDescription: String {
        return """
        production {
            goal: \(self.goal)
            rule: \(self.rule.map { $0.description } )
        }
        """
    }
}
