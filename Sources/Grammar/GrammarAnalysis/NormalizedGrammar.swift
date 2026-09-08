import Foundation

/// A stable identity carried by a normalized production across parser engines.
///
/// `GrammarNormalizedModel.init(grammar:)` assigns deterministic occurrence
/// identities (`p1`, `p2`, …). Corpus and editor adapters should supply their
/// own durable identities when they need identities to survive source edits.
public struct GrammarProductionID: RawRepresentable, Hashable, Codable, Sendable,
    Comparable, CustomStringConvertible {
    public let rawValue: String

    public init(rawValue: String) {
        self.rawValue = rawValue
    }

    public var description: String { rawValue }

    public static func < (lhs: Self, rhs: Self) -> Bool {
        lhs.rawValue < rhs.rawValue
    }

    public init(from decoder: Decoder) throws {
        self.init(rawValue: try decoder.singleValueContainer().decode(String.self))
    }

    public func encode(to encoder: Encoder) throws {
        var container = encoder.singleValueContainer()
        try container.encode(rawValue)
    }
}

/// An engine-neutral, lossless terminal description.
public enum GrammarNormalizedTerminal: Hashable, Codable, Sendable {
    case literal(String)
    case literals([String])
    case characterRange(lower: Character, upper: Character)
    case regularExpression(String)
    case boundary(String)

    fileprivate init(_ terminal: Terminal) {
        switch terminal {
        case .string(let value):
            self = .literal(value)
        case .stringList(let values):
            self = .literals(values)
        case .characterRange(let range):
            self = .characterRange(lower: range.lowerBound, upper: range.upperBound)
        case .regularExpression(let expression):
            self = .regularExpression(expression.pattern)
        case .meta(let value):
            self = .boundary(value.rawValue)
        }
    }

    fileprivate var orderingKey: String {
        switch self {
        case .literal(let value): "literal\u{1f}\(value)"
        case .literals(let values): "literals\u{1f}\(values.joined(separator: "\u{1e}"))"
        case .characterRange(let lower, let upper): "range\u{1f}\(lower)\u{1f}\(upper)"
        case .regularExpression(let value): "regex\u{1f}\(value)"
        case .boundary(let value): "boundary\u{1f}\(value)"
        }
    }

    fileprivate var denotesEpsilon: Bool {
        switch self {
        case .literal(let value): value.isEmpty
        case .literals(let values): values.allSatisfy(\.isEmpty)
        case .regularExpression(let pattern): pattern.isEmpty
        case .boundary(let value): value.isEmpty || value == "ε" || value == "λ"
        case .characterRange: false
        }
    }
}

extension GrammarNormalizedTerminal {
    private enum CodingKeys: String, CodingKey { case kind, value, values, lower, upper, pattern }
    private enum Kind: String, Codable { case literal, literals, characterRange, regularExpression, boundary }

    public init(from decoder: Decoder) throws {
        let values = try decoder.container(keyedBy: CodingKeys.self)
        switch try values.decode(Kind.self, forKey: .kind) {
        case .literal:
            self = .literal(try values.decode(String.self, forKey: .value))
        case .literals:
            self = .literals(try values.decode([String].self, forKey: .values))
        case .characterRange:
            let lower = try values.decode(String.self, forKey: .lower)
            let upper = try values.decode(String.self, forKey: .upper)
            guard lower.count == 1, upper.count == 1,
                  let lowerCharacter = lower.first, let upperCharacter = upper.first else {
                throw DecodingError.dataCorruptedError(
                    forKey: .lower, in: values,
                    debugDescription: "A normalized character range requires one Character per bound."
                )
            }
            self = .characterRange(lower: lowerCharacter, upper: upperCharacter)
        case .regularExpression:
            self = .regularExpression(try values.decode(String.self, forKey: .pattern))
        case .boundary:
            self = .boundary(try values.decode(String.self, forKey: .value))
        }
    }

    public func encode(to encoder: Encoder) throws {
        var values = encoder.container(keyedBy: CodingKeys.self)
        switch self {
        case .literal(let value):
            try values.encode(Kind.literal, forKey: .kind)
            try values.encode(value, forKey: .value)
        case .literals(let alternatives):
            try values.encode(Kind.literals, forKey: .kind)
            try values.encode(alternatives, forKey: .values)
        case .characterRange(let lower, let upper):
            try values.encode(Kind.characterRange, forKey: .kind)
            try values.encode(String(lower), forKey: .lower)
            try values.encode(String(upper), forKey: .upper)
        case .regularExpression(let pattern):
            try values.encode(Kind.regularExpression, forKey: .kind)
            try values.encode(pattern, forKey: .pattern)
        case .boundary(let value):
            try values.encode(Kind.boundary, forKey: .kind)
            try values.encode(value, forKey: .value)
        }
    }
}

extension GrammarNormalizedTerminal: Comparable {
    public static func < (lhs: Self, rhs: Self) -> Bool {
        lhs.orderingKey < rhs.orderingKey
    }
}

/// A terminal or nonterminal in the canonical, parser-facing grammar model.
public enum GrammarNormalizedSymbol: Hashable, Codable, Sendable {
    case terminal(GrammarNormalizedTerminal)
    case nonterminal(String)

    fileprivate var orderingKey: String {
        switch self {
        case .terminal(let terminal): "terminal\u{1f}\(terminal.orderingKey)"
        case .nonterminal(let name): "nonterminal\u{1f}\(name)"
        }
    }
}

extension GrammarNormalizedSymbol {
    private enum CodingKeys: String, CodingKey { case kind, terminal, name }
    private enum Kind: String, Codable { case terminal, nonterminal }

    public init(from decoder: Decoder) throws {
        let values = try decoder.container(keyedBy: CodingKeys.self)
        switch try values.decode(Kind.self, forKey: .kind) {
        case .terminal:
            self = .terminal(try values.decode(GrammarNormalizedTerminal.self, forKey: .terminal))
        case .nonterminal:
            self = .nonterminal(try values.decode(String.self, forKey: .name))
        }
    }

    public func encode(to encoder: Encoder) throws {
        var values = encoder.container(keyedBy: CodingKeys.self)
        switch self {
        case .terminal(let terminal):
            try values.encode(Kind.terminal, forKey: .kind)
            try values.encode(terminal, forKey: .terminal)
        case .nonterminal(let name):
            try values.encode(Kind.nonterminal, forKey: .kind)
            try values.encode(name, forKey: .name)
        }
    }
}

extension GrammarNormalizedSymbol: Comparable {
    public static func < (lhs: Self, rhs: Self) -> Bool {
        lhs.orderingKey < rhs.orderingKey
    }
}

public struct GrammarNormalizedProduction: Identifiable, Hashable, Codable, Sendable {
    public let id: GrammarProductionID
    public let lhs: String
    public let rhs: [GrammarNormalizedSymbol]

    public init(id: GrammarProductionID, lhs: String, rhs: [GrammarNormalizedSymbol]) {
        self.id = id
        self.lhs = lhs
        self.rhs = rhs
    }
}

public struct GrammarLexicalDefinition: Identifiable, Hashable, Codable, Sendable {
    public let name: String
    public let terminal: GrammarNormalizedTerminal
    public var id: String { name }

    public init(name: String, terminal: GrammarNormalizedTerminal) {
        self.name = name
        self.terminal = terminal
    }
}

public enum GrammarPrecedenceAssociativity: String, Hashable, Codable, Sendable {
    case left
    case right
    case nonassociative
}

/// One ordered precedence level. Higher numeric levels bind more tightly.
public struct GrammarPrecedenceLevel: Identifiable, Hashable, Codable, Sendable {
    public let level: Int
    public let associativity: GrammarPrecedenceAssociativity
    public let terminals: [GrammarNormalizedTerminal]
    public var id: Int { level }

    public init(
        level: Int,
        associativity: GrammarPrecedenceAssociativity,
        terminals: [GrammarNormalizedTerminal]
    ) {
        self.level = level
        self.associativity = associativity
        self.terminals = terminals
    }
}

public enum GrammarNormalizationError: Error, Equatable, Sendable, LocalizedError {
    case unsupportedSchema(Int)
    case emptyStartSymbol
    case emptyNonterminal(production: GrammarProductionID)
    case emptyProductionIdentity
    case duplicateProductionIdentity(GrammarProductionID)
    case productionIdentityCount(expected: Int, actual: Int)
    case metaSymbol(production: GrammarProductionID, symbol: String)
    case epsilonTerminal(production: GrammarProductionID)
    case emptyLexicalDefinition
    case duplicateLexicalDefinition(String)
    case invalidPrecedenceLevel(Int)
    case duplicatePrecedenceLevel(Int)

    public var errorDescription: String? {
        switch self {
        case .unsupportedSchema(let version):
            "Normalized grammar schema \(version) is not supported."
        case .emptyStartSymbol:
            "The normalized grammar start symbol must not be empty."
        case .emptyNonterminal(let production):
            "Production \(production) contains an empty nonterminal name."
        case .emptyProductionIdentity:
            "A normalized production identity must not be empty."
        case .duplicateProductionIdentity(let identity):
            "Production identity \(identity) is duplicated."
        case .productionIdentityCount(let expected, let actual):
            "Expected \(expected) production identities, but received \(actual)."
        case .metaSymbol(let production, let symbol):
            "Production \(production) still contains the EBNF meta-symbol \(symbol)."
        case .epsilonTerminal(let production):
            "Production \(production) contains an explicit epsilon terminal; use an empty right-hand side."
        case .emptyLexicalDefinition:
            "A normalized lexical definition name must not be empty."
        case .duplicateLexicalDefinition(let name):
            "Lexical definition \(name) is duplicated."
        case .invalidPrecedenceLevel(let level):
            "Precedence level \(level) must be positive and contain at least one terminal."
        case .duplicatePrecedenceLevel(let level):
            "Precedence level \(level) is duplicated."
        }
    }
}

/// Versioned, engine-neutral input for parser construction and grammar analysis.
///
/// The model preserves production order and duplicate occurrences. Epsilon has
/// exactly one representation: an empty production right-hand side.
public struct GrammarNormalizedModel: Hashable, Codable, Sendable {
    public static let currentSchemaVersion = 1

    public let schemaVersion: Int
    public let startSymbol: String
    public let productions: [GrammarNormalizedProduction]
    public let lexicalDefinitions: [GrammarLexicalDefinition]
    public let precedence: [GrammarPrecedenceLevel]
    public let generatedNonterminals: [String]
    public let epsilonSymbol: String
    public let endOfInputSymbol: String

    public init(
        schemaVersion: Int = GrammarNormalizedModel.currentSchemaVersion,
        startSymbol: String,
        productions: [GrammarNormalizedProduction],
        lexicalDefinitions: [GrammarLexicalDefinition] = [],
        precedence: [GrammarPrecedenceLevel] = [],
        generatedNonterminals: [String] = [],
        epsilonSymbol: String = "ε",
        endOfInputSymbol: String = "$"
    ) throws {
        self.schemaVersion = schemaVersion
        self.startSymbol = startSymbol
        self.productions = productions
        self.lexicalDefinitions = lexicalDefinitions.sorted { $0.name < $1.name }
        self.precedence = precedence.sorted { $0.level < $1.level }
        self.generatedNonterminals = Array(Set(generatedNonterminals)).sorted()
        self.epsilonSymbol = epsilonSymbol
        self.endOfInputSymbol = endOfInputSymbol
        try validate()
    }

    public init(grammar: Grammar, productionIDs: [GrammarProductionID]? = nil) throws {
        if let productionIDs, productionIDs.count != grammar.productions.count {
            throw GrammarNormalizationError.productionIdentityCount(
                expected: grammar.productions.count, actual: productionIDs.count
            )
        }
        let identities = productionIDs
            ?? grammar.productions.indices.map { GrammarProductionID(rawValue: "p\($0 + 1)") }
        let normalized = try zip(grammar.productions, identities).map { production, identity in
            let rhs = try production.rule.map { symbol -> GrammarNormalizedSymbol in
                switch symbol {
                case .terminal(let terminal):
                    return .terminal(.init(terminal))
                case .nonTerminal(let nonterminal):
                    return .nonterminal(nonterminal.name)
                case .metaSymbol(let meta):
                    throw GrammarNormalizationError.metaSymbol(
                        production: identity, symbol: meta.rawValue
                    )
                }
            }
            return GrammarNormalizedProduction(
                id: identity, lhs: production.goal.name, rhs: rhs
            )
        }
        try self.init(
            startSymbol: grammar.start.name,
            productions: normalized,
            lexicalDefinitions: grammar.lexicalTokens.map {
                GrammarLexicalDefinition(name: $0.key, terminal: .init($0.value))
            },
            generatedNonterminals: grammar.generatedNonTerminals.map(\.name),
            epsilonSymbol: grammar.epsilon.rawValue,
            endOfInputSymbol: grammar.endofile.rawValue
        )
    }

    private enum CodingKeys: String, CodingKey {
        case schemaVersion, startSymbol, productions, lexicalDefinitions,
             precedence, generatedNonterminals, epsilonSymbol, endOfInputSymbol
    }

    public init(from decoder: Decoder) throws {
        let values = try decoder.container(keyedBy: CodingKeys.self)
        try self.init(
            schemaVersion: values.decode(Int.self, forKey: .schemaVersion),
            startSymbol: values.decode(String.self, forKey: .startSymbol),
            productions: values.decode([GrammarNormalizedProduction].self, forKey: .productions),
            lexicalDefinitions: values.decodeIfPresent(
                [GrammarLexicalDefinition].self, forKey: .lexicalDefinitions
            ) ?? [],
            precedence: values.decodeIfPresent(
                [GrammarPrecedenceLevel].self, forKey: .precedence
            ) ?? [],
            generatedNonterminals: values.decodeIfPresent(
                [String].self, forKey: .generatedNonterminals
            ) ?? [],
            epsilonSymbol: values.decodeIfPresent(String.self, forKey: .epsilonSymbol) ?? "ε",
            endOfInputSymbol: values.decodeIfPresent(String.self, forKey: .endOfInputSymbol) ?? "$"
        )
    }

    private func validate() throws {
        guard schemaVersion == Self.currentSchemaVersion else {
            throw GrammarNormalizationError.unsupportedSchema(schemaVersion)
        }
        guard !startSymbol.isEmpty else { throw GrammarNormalizationError.emptyStartSymbol }
        var identities: Set<GrammarProductionID> = []
        for production in productions {
            guard !production.id.rawValue.isEmpty else {
                throw GrammarNormalizationError.emptyProductionIdentity
            }
            guard !production.lhs.isEmpty,
                  !production.rhs.contains(where: {
                      if case .nonterminal(let name) = $0 { return name.isEmpty }
                      return false
                  }) else {
                throw GrammarNormalizationError.emptyNonterminal(production: production.id)
            }
            guard identities.insert(production.id).inserted else {
                throw GrammarNormalizationError.duplicateProductionIdentity(production.id)
            }
            if production.rhs.contains(where: { symbol in
                guard case .terminal(let terminal) = symbol else { return false }
                return terminal.denotesEpsilon
            }) {
                throw GrammarNormalizationError.epsilonTerminal(production: production.id)
            }
        }
        var lexicalNames: Set<String> = []
        for definition in lexicalDefinitions {
            guard !definition.name.isEmpty else {
                throw GrammarNormalizationError.emptyLexicalDefinition
            }
            guard lexicalNames.insert(definition.name).inserted else {
                throw GrammarNormalizationError.duplicateLexicalDefinition(definition.name)
            }
        }
        var precedenceLevels: Set<Int> = []
        for declaration in precedence {
            guard declaration.level > 0, !declaration.terminals.isEmpty else {
                throw GrammarNormalizationError.invalidPrecedenceLevel(declaration.level)
            }
            guard precedenceLevels.insert(declaration.level).inserted else {
                throw GrammarNormalizationError.duplicatePrecedenceLevel(declaration.level)
            }
        }
    }
}

public extension Grammar {
    /// Produces the canonical parser-facing representation of this grammar.
    func normalizedModel(productionIDs: [GrammarProductionID]? = nil) throws
        -> GrammarNormalizedModel {
        try GrammarNormalizedModel(grammar: self, productionIDs: productionIDs)
    }
}

public enum GrammarLookahead: Hashable, Codable, Sendable, Comparable {
    case terminal(GrammarNormalizedTerminal)
    case epsilon
    case endOfInput

    private var orderingKey: String {
        switch self {
        case .terminal(let terminal): "terminal\u{1f}\(terminal.orderingKey)"
        case .epsilon: "epsilon"
        case .endOfInput: "end-of-input"
        }
    }

    public static func < (lhs: Self, rhs: Self) -> Bool {
        lhs.orderingKey < rhs.orderingKey
    }
}

extension GrammarLookahead {
    private enum CodingKeys: String, CodingKey { case kind, terminal }
    private enum Kind: String, Codable { case terminal, epsilon, endOfInput }

    public init(from decoder: Decoder) throws {
        let values = try decoder.container(keyedBy: CodingKeys.self)
        switch try values.decode(Kind.self, forKey: .kind) {
        case .terminal:
            self = .terminal(try values.decode(GrammarNormalizedTerminal.self, forKey: .terminal))
        case .epsilon:
            self = .epsilon
        case .endOfInput:
            self = .endOfInput
        }
    }

    public func encode(to encoder: Encoder) throws {
        var values = encoder.container(keyedBy: CodingKeys.self)
        switch self {
        case .terminal(let terminal):
            try values.encode(Kind.terminal, forKey: .kind)
            try values.encode(terminal, forKey: .terminal)
        case .epsilon:
            try values.encode(Kind.epsilon, forKey: .kind)
        case .endOfInput:
            try values.encode(Kind.endOfInput, forKey: .kind)
        }
    }
}

public struct GrammarNonterminalLookaheads: Identifiable, Hashable, Codable, Sendable {
    public let nonterminal: String
    public let lookaheads: [GrammarLookahead]
    public var id: String { nonterminal }
}

public struct GrammarDependency: Hashable, Codable, Sendable, Comparable {
    public let from: String
    public let to: String

    public static func < (lhs: Self, rhs: Self) -> Bool {
        (lhs.from, lhs.to) < (rhs.from, rhs.to)
    }
}

public struct GrammarDuplicateProductions: Identifiable, Hashable, Codable, Sendable {
    public let lhs: String
    public let rhs: [GrammarNormalizedSymbol]
    public let productionIDs: [GrammarProductionID]
    public var id: GrammarProductionID {
        productionIDs.first ?? GrammarProductionID(rawValue: "")
    }
}

public struct GrammarPredictiveConflict: Identifiable, Hashable, Codable, Sendable {
    public let nonterminal: String
    public let firstProduction: GrammarProductionID
    public let secondProduction: GrammarProductionID
    public let lookaheads: [GrammarLookahead]
    public var id: String { "\(firstProduction.rawValue)\u{1f}\(secondProduction.rawValue)" }
}

/// A deterministic structural and predictive analysis of a normalized grammar.
public struct GrammarNormalizedAnalysis: Hashable, Codable, Sendable {
    public let startSymbol: String
    public let definedNonterminals: [String]
    public let referencedNonterminals: [String]
    public let undefinedNonterminals: [String]
    public let reachableNonterminals: [String]
    public let unreachableNonterminals: [String]
    public let productiveNonterminals: [String]
    public let unproductiveNonterminals: [String]
    public let nullableNonterminals: [String]
    public let directlyLeftRecursiveNonterminals: [String]
    public let recursiveComponents: [[String]]
    public let unusedLexicalDefinitions: [String]
    public let dependencies: [GrammarDependency]
    public let duplicateProductions: [GrammarDuplicateProductions]
    public let first: [GrammarNonterminalLookaheads]
    public let follow: [GrammarNonterminalLookaheads]
    public let predictiveConflicts: [GrammarPredictiveConflict]

    public var isLL1: Bool {
        undefinedNonterminals.isEmpty
            && recursiveComponents.isEmpty
            && predictiveConflicts.isEmpty
    }
}

public extension GrammarNormalizedModel {
    func analyze() -> GrammarNormalizedAnalysis {
        GrammarNormalizedAnalyzer.analyze(self)
    }
}

public extension Grammar {
    func normalizedAnalysis(productionIDs: [GrammarProductionID]? = nil) throws
        -> GrammarNormalizedAnalysis {
        try normalizedModel(productionIDs: productionIDs).analyze()
    }
}

private enum GrammarNormalizedAnalyzer {
    static func analyze(_ grammar: GrammarNormalizedModel) -> GrammarNormalizedAnalysis {
        let defined = Set(grammar.productions.map(\.lhs))
        let referenced = Set(grammar.productions.flatMap { production in
            production.rhs.compactMap { symbol -> String? in
                if case .nonterminal(let name) = symbol { return name }
                return nil
            }
        })
        let all = defined.union(referenced).union([grammar.startSymbol])
        let byLHS = Dictionary(grouping: grammar.productions, by: \.lhs)
        let dependencies = Set(grammar.productions.flatMap { production in
            production.rhs.compactMap { symbol -> GrammarDependency? in
                if case .nonterminal(let name) = symbol {
                    return GrammarDependency(from: production.lhs, to: name)
                }
                return nil
            }
        })
        let adjacency = Dictionary(grouping: dependencies, by: \.from)
            .mapValues { Set($0.map(\.to)) }

        let reachable = reachableSymbols(from: grammar.startSymbol, adjacency: adjacency)
        let nullable = fixedPoint(seed: []) { result in
            for production in grammar.productions where production.rhs.allSatisfy({ symbol in
                if case .nonterminal(let name) = symbol { return result.contains(name) }
                return false
            }) {
                result.insert(production.lhs)
            }
        }
        let productive = fixedPoint(seed: []) { result in
            for production in grammar.productions where production.rhs.allSatisfy({ symbol in
                switch symbol {
                case .terminal: true
                case .nonterminal(let name): result.contains(name)
                }
            }) {
                result.insert(production.lhs)
            }
        }
        let (firstSets, followSets) = firstAndFollow(
            grammar, allNonterminals: all, nullable: nullable
        )
        let conflicts = predictiveConflicts(
            grammar, productionsByLHS: byLHS, nullable: nullable,
            first: firstSets, follow: followSets
        )
        let duplicates = Dictionary(grouping: grammar.productions) {
            ProductionShape(lhs: $0.lhs, rhs: $0.rhs)
        }.values.filter { $0.count > 1 }.map { productions in
            GrammarDuplicateProductions(
                lhs: productions[0].lhs, rhs: productions[0].rhs,
                productionIDs: productions.map(\.id).sorted()
            )
        }.sorted { $0.id < $1.id }
        let usedTerminals = Set(grammar.productions.flatMap { production in
            production.rhs.compactMap { symbol -> GrammarNormalizedTerminal? in
                if case .terminal(let terminal) = symbol { return terminal }
                return nil
            }
        })

        return GrammarNormalizedAnalysis(
            startSymbol: grammar.startSymbol,
            definedNonterminals: defined.sorted(),
            referencedNonterminals: referenced.sorted(),
            undefinedNonterminals: referenced.union([grammar.startSymbol]).subtracting(defined).sorted(),
            reachableNonterminals: reachable.intersection(defined).sorted(),
            unreachableNonterminals: defined.subtracting(reachable).sorted(),
            productiveNonterminals: productive.sorted(),
            unproductiveNonterminals: defined.subtracting(productive).sorted(),
            nullableNonterminals: nullable.sorted(),
            directlyLeftRecursiveNonterminals: Set(grammar.productions.compactMap {
                $0.rhs.first == .nonterminal($0.lhs) ? $0.lhs : nil
            }).sorted(),
            recursiveComponents: stronglyConnectedComponents(nodes: all, adjacency: adjacency),
            unusedLexicalDefinitions: grammar.lexicalDefinitions.filter {
                !usedTerminals.contains($0.terminal)
            }.map(\.name),
            dependencies: dependencies.sorted(),
            duplicateProductions: duplicates,
            first: lookaheadEntries(firstSets),
            follow: lookaheadEntries(followSets),
            predictiveConflicts: conflicts
        )
    }

    private struct ProductionShape: Hashable {
        let lhs: String
        let rhs: [GrammarNormalizedSymbol]
    }

    private static func fixedPoint(
        seed: Set<String>, update: (inout Set<String>) -> Void
    ) -> Set<String> {
        var result = seed
        var previousCount: Int
        repeat {
            previousCount = result.count
            update(&result)
        } while result.count != previousCount
        return result
    }

    private static func reachableSymbols(
        from start: String, adjacency: [String: Set<String>]
    ) -> Set<String> {
        var reached: Set<String> = []
        var pending = [start]
        while let current = pending.popLast() {
            guard reached.insert(current).inserted else { continue }
            pending.append(contentsOf: adjacency[current, default: []].sorted().reversed())
        }
        return reached
    }

    private static func firstAndFollow(
        _ grammar: GrammarNormalizedModel,
        allNonterminals: Set<String>, nullable: Set<String>
    ) -> ([String: Set<GrammarLookahead>], [String: Set<GrammarLookahead>]) {
        var first = Dictionary(uniqueKeysWithValues: allNonterminals.map { ($0, Set<GrammarLookahead>()) })
        var changed = true
        while changed {
            changed = false
            for production in grammar.productions {
                let before = first[production.lhs, default: []].count
                first[production.lhs, default: []].formUnion(
                    firstOf(production.rhs, first: first, nullable: nullable)
                )
                if first[production.lhs, default: []].count != before { changed = true }
            }
        }

        var follow = Dictionary(uniqueKeysWithValues: allNonterminals.map { ($0, Set<GrammarLookahead>()) })
        follow[grammar.startSymbol, default: []].insert(.endOfInput)
        changed = true
        while changed {
            changed = false
            for production in grammar.productions {
                for (index, symbol) in production.rhs.enumerated() {
                    guard case .nonterminal(let name) = symbol else { continue }
                    let suffix = Array(production.rhs.dropFirst(index + 1))
                    let suffixFirst = firstOf(suffix, first: first, nullable: nullable)
                    let before = follow[name, default: []].count
                    follow[name, default: []].formUnion(suffixFirst.filter { $0 != .epsilon })
                    if suffixFirst.contains(.epsilon) {
                        follow[name, default: []].formUnion(follow[production.lhs, default: []])
                    }
                    if follow[name, default: []].count != before { changed = true }
                }
            }
        }
        return (first, follow)
    }

    private static func firstOf(
        _ symbols: [GrammarNormalizedSymbol],
        first: [String: Set<GrammarLookahead>], nullable: Set<String>
    ) -> Set<GrammarLookahead> {
        guard !symbols.isEmpty else { return [.epsilon] }
        var result: Set<GrammarLookahead> = []
        for symbol in symbols {
            switch symbol {
            case .terminal(let terminal):
                result.insert(.terminal(terminal))
                return result
            case .nonterminal(let name):
                result.formUnion(first[name, default: []].filter { $0 != .epsilon })
                if !nullable.contains(name) { return result }
            }
        }
        result.insert(.epsilon)
        return result
    }

    private static func predictiveConflicts(
        _ grammar: GrammarNormalizedModel,
        productionsByLHS: [String: [GrammarNormalizedProduction]],
        nullable: Set<String>,
        first: [String: Set<GrammarLookahead>],
        follow: [String: Set<GrammarLookahead>]
    ) -> [GrammarPredictiveConflict] {
        var result: [GrammarPredictiveConflict] = []
        for lhs in productionsByLHS.keys.sorted() {
            let productions = productionsByLHS[lhs, default: []]
            let predictions = productions.map { production -> Set<GrammarLookahead> in
                var set = firstOf(production.rhs, first: first, nullable: nullable)
                if set.remove(.epsilon) != nil { set.formUnion(follow[lhs, default: []]) }
                return set
            }
            for firstIndex in productions.indices {
                for secondIndex in productions.indices where secondIndex > firstIndex {
                    let overlap = predictions[firstIndex].intersection(predictions[secondIndex])
                    if !overlap.isEmpty {
                        result.append(GrammarPredictiveConflict(
                            nonterminal: lhs,
                            firstProduction: productions[firstIndex].id,
                            secondProduction: productions[secondIndex].id,
                            lookaheads: overlap.sorted()
                        ))
                    }
                }
            }
        }
        return result
    }

    private static func lookaheadEntries(
        _ sets: [String: Set<GrammarLookahead>]
    ) -> [GrammarNonterminalLookaheads] {
        sets.keys.sorted().map {
            GrammarNonterminalLookaheads(nonterminal: $0, lookaheads: sets[$0, default: []].sorted())
        }
    }

    private static func stronglyConnectedComponents(
        nodes: Set<String>, adjacency: [String: Set<String>]
    ) -> [[String]] {
        var nextIndex = 0
        var indices: [String: Int] = [:]
        var lowlinks: [String: Int] = [:]
        var stack: [String] = []
        var onStack: Set<String> = []
        var result: [[String]] = []

        func visit(_ node: String) {
            indices[node] = nextIndex
            lowlinks[node] = nextIndex
            nextIndex += 1
            stack.append(node)
            onStack.insert(node)

            for neighbor in adjacency[node, default: []].sorted() {
                if indices[neighbor] == nil {
                    visit(neighbor)
                    if let nodeLowlink = lowlinks[node], let neighborLowlink = lowlinks[neighbor] {
                        lowlinks[node] = min(nodeLowlink, neighborLowlink)
                    }
                } else if onStack.contains(neighbor) {
                    if let nodeLowlink = lowlinks[node], let neighborIndex = indices[neighbor] {
                        lowlinks[node] = min(nodeLowlink, neighborIndex)
                    }
                }
            }
            if lowlinks[node] == indices[node] {
                var component: [String] = []
                while let member = stack.popLast() {
                    onStack.remove(member)
                    component.append(member)
                    if member == node { break }
                }
                component.sort()
                let recursive = component.count > 1
                    || adjacency[component[0], default: []].contains(component[0])
                if recursive { result.append(component) }
            }
        }

        for node in nodes.sorted() where indices[node] == nil { visit(node) }
        return result.sorted { ($0.first ?? "") < ($1.first ?? "") }
    }
}
