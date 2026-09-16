import Foundation

/// Metamorphic relations whose construction and structural verification belong to Grammar.
public enum GrammarExecutableLaw: String, CaseIterable, Codable, Sendable {
    /// Changing production declaration order must not change the recognized language.
    case productionPermutation
    /// A collision-free bijective renaming must preserve grammar structure and language.
    case nonterminalAlphaRenaming
}

public struct GrammarNonterminalRename: Hashable, Codable, Sendable, Comparable {
    public let from: String
    public let to: String

    public init(from: String, to: String) {
        self.from = from
        self.to = to
    }

    public static func < (lhs: Self, rhs: Self) -> Bool {
        (lhs.from, lhs.to) < (rhs.from, rhs.to)
    }
}

/// A self-contained input pair for parser-level metamorphic testing.
///
/// Grammar verifies that `candidate` is exactly the declared structural transformation.
/// Parser engines remain responsible for demonstrating equivalent observations.
public struct GrammarLawWitness: Hashable, Codable, Sendable {
    public static let currentSchemaVersion = 1
    public static let kindIdentifier = "grammar-executable-law-witness"

    public let schemaVersion: Int
    public let kind: String
    public let id: String
    public let law: GrammarExecutableLaw
    public let baseline: GrammarNormalizedModel
    public let candidate: GrammarNormalizedModel
    public let renames: [GrammarNonterminalRename]

    public init(
        id: String,
        law: GrammarExecutableLaw,
        baseline: GrammarNormalizedModel,
        candidate: GrammarNormalizedModel,
        renames: [GrammarNonterminalRename] = []
    ) throws {
        self.schemaVersion = Self.currentSchemaVersion
        self.kind = Self.kindIdentifier
        self.id = id
        self.law = law
        self.baseline = baseline
        self.candidate = candidate
        self.renames = renames.sorted()
        try GrammarLawVerifier.requireValid(self)
    }

    private enum CodingKeys: String, CodingKey {
        case schemaVersion, kind, id, law, baseline, candidate, renames
    }

    public init(from decoder: Decoder) throws {
        let values = try decoder.container(keyedBy: CodingKeys.self)
        let schemaVersion = try values.decode(Int.self, forKey: .schemaVersion)
        let kind = try values.decode(String.self, forKey: .kind)
        guard schemaVersion == Self.currentSchemaVersion else {
            throw GrammarLawError.unsupportedSchema(schemaVersion)
        }
        guard kind == Self.kindIdentifier else { throw GrammarLawError.unsupportedKind(kind) }
        try self.init(
            id: values.decode(String.self, forKey: .id),
            law: values.decode(GrammarExecutableLaw.self, forKey: .law),
            baseline: values.decode(GrammarNormalizedModel.self, forKey: .baseline),
            candidate: values.decode(GrammarNormalizedModel.self, forKey: .candidate),
            renames: values.decodeIfPresent(
                [GrammarNonterminalRename].self, forKey: .renames
            ) ?? []
        )
    }
}

public struct GrammarLawEvaluation: Hashable, Codable, Sendable {
    public let witnessID: String
    public let law: GrammarExecutableLaw
    public let passed: Bool
    public let violations: [String]

    public init(
        witnessID: String,
        law: GrammarExecutableLaw,
        passed: Bool,
        violations: [String]
    ) {
        self.witnessID = witnessID
        self.law = law
        self.passed = passed
        self.violations = violations
    }
}

public enum GrammarLawError: Error, Equatable, Sendable, LocalizedError {
    case unsupportedSchema(Int)
    case unsupportedKind(String)
    case emptyIdentity
    case invalidProductionPermutation
    case emptyRenaming
    case invalidRenameSource(String)
    case invalidRenameTarget(String)
    case collidingRenameTarget(String)
    case malformedWitness([String])

    public var errorDescription: String? {
        switch self {
        case .unsupportedSchema(let version):
            "Grammar law witness schema \(version) is not supported."
        case .unsupportedKind(let kind):
            "Grammar law witness kind ‘\(kind)’ is not supported."
        case .emptyIdentity:
            "A grammar law witness requires a non-empty identity."
        case .invalidProductionPermutation:
            "A production permutation must contain every production identity exactly once and change the order."
        case .emptyRenaming:
            "An alpha-renaming law requires at least one changed nonterminal."
        case .invalidRenameSource(let name):
            "The alpha-renaming source ‘\(name)’ is not a grammar nonterminal."
        case .invalidRenameTarget(let name):
            "The alpha-renaming target ‘\(name)’ is empty or unchanged."
        case .collidingRenameTarget(let name):
            "The alpha-renaming target ‘\(name)’ collides with another nonterminal."
        case .malformedWitness(let violations):
            "Grammar law witness is malformed: \(violations.joined(separator: "; "))"
        }
    }
}

public enum GrammarLawTransformer {
    public static func permuteProductions(
        _ model: GrammarNormalizedModel,
        order: [GrammarProductionID],
        id: String
    ) throws -> GrammarLawWitness {
        let byID = Dictionary(uniqueKeysWithValues: model.productions.map { ($0.id, $0) })
        guard order.count == model.productions.count,
              Set(order).count == order.count,
              Set(order) == Set(byID.keys),
              order != model.productions.map(\.id) else {
            throw GrammarLawError.invalidProductionPermutation
        }
        let candidate = try rebuild(model, productions: order.compactMap { byID[$0] })
        return try GrammarLawWitness(
            id: id, law: .productionPermutation, baseline: model, candidate: candidate
        )
    }

    public static func alphaRenameNonterminals(
        _ model: GrammarNormalizedModel,
        renames: [GrammarNonterminalRename],
        id: String
    ) throws -> GrammarLawWitness {
        let mapping = try validatedMapping(renames, model: model)
        let candidate = try applyAlphaRenaming(model, mapping: mapping)
        return try GrammarLawWitness(
            id: id, law: .nonterminalAlphaRenaming, baseline: model,
            candidate: candidate, renames: renames
        )
    }

    private static func applyAlphaRenaming(
        _ model: GrammarNormalizedModel,
        mapping: [String: String]
    ) throws -> GrammarNormalizedModel {
        let renamedProductions = model.productions.map { production in
            GrammarNormalizedProduction(
                id: production.id,
                lhs: mapping[production.lhs] ?? production.lhs,
                rhs: production.rhs.map { symbol in
                    guard case .nonterminal(let name) = symbol else { return symbol }
                    return .nonterminal(mapping[name] ?? name)
                }
            )
        }
        return try rebuild(
            model,
            startSymbol: mapping[model.startSymbol] ?? model.startSymbol,
            productions: renamedProductions,
            generatedNonterminals: model.generatedNonterminals.map { mapping[$0] ?? $0 }
        )
    }

    fileprivate static func transformedBaseline(
        for witness: GrammarLawWitness
    ) throws -> GrammarNormalizedModel {
        switch witness.law {
        case .productionPermutation:
            return try rebuild(witness.baseline, productions: witness.candidate.productions)
        case .nonterminalAlphaRenaming:
            let mapping = try validatedMapping(witness.renames, model: witness.baseline)
            return try applyAlphaRenaming(witness.baseline, mapping: mapping)
        }
    }

    private static func validatedMapping(
        _ renames: [GrammarNonterminalRename], model: GrammarNormalizedModel
    ) throws -> [String: String] {
        guard !renames.isEmpty else { throw GrammarLawError.emptyRenaming }
        let universe = nonterminals(in: model)
        var mapping: [String: String] = [:]
        for rename in renames {
            guard universe.contains(rename.from) else {
                throw GrammarLawError.invalidRenameSource(rename.from)
            }
            guard !rename.to.isEmpty, rename.from != rename.to else {
                throw GrammarLawError.invalidRenameTarget(rename.to)
            }
            guard mapping.updateValue(rename.to, forKey: rename.from) == nil else {
                throw GrammarLawError.invalidRenameSource(rename.from)
            }
        }
        let targets = Array(mapping.values)
        guard Set(targets).count == targets.count else {
            throw GrammarLawError.collidingRenameTarget(
                targets.first { target in targets.count(where: { $0 == target }) > 1 } ?? ""
            )
        }
        let untouched = universe.subtracting(mapping.keys)
        if let collision = targets.first(where: untouched.contains) {
            throw GrammarLawError.collidingRenameTarget(collision)
        }
        return mapping
    }

    private static func nonterminals(in model: GrammarNormalizedModel) -> Set<String> {
        Set(model.productions.map(\.lhs))
            .union(model.productions.flatMap { production in
                production.rhs.compactMap { symbol in
                    guard case .nonterminal(let name) = symbol else { return nil }
                    return name
                }
            })
            .union([model.startSymbol])
            .union(model.generatedNonterminals)
    }

    private static func rebuild(
        _ model: GrammarNormalizedModel,
        startSymbol: String? = nil,
        productions: [GrammarNormalizedProduction],
        generatedNonterminals: [String]? = nil
    ) throws -> GrammarNormalizedModel {
        try GrammarNormalizedModel(
            startSymbol: startSymbol ?? model.startSymbol,
            productions: productions,
            lexicalDefinitions: model.lexicalDefinitions,
            precedence: model.precedence,
            generatedNonterminals: generatedNonterminals ?? model.generatedNonterminals,
            epsilonSymbol: model.epsilonSymbol,
            endOfInputSymbol: model.endOfInputSymbol
        )
    }
}

public enum GrammarLawVerifier {
    public static func evaluate(_ witness: GrammarLawWitness) -> GrammarLawEvaluation {
        var violations: [String] = []
        if witness.id.isEmpty { violations.append("witness identity is empty") }
        switch witness.law {
        case .productionPermutation:
            if !witness.renames.isEmpty { violations.append("permutation carries renames") }
            if witness.baseline.productions.map(\.id) == witness.candidate.productions.map(\.id) {
                violations.append("production order did not change")
            }
        case .nonterminalAlphaRenaming:
            if witness.renames.isEmpty { violations.append("renaming is empty") }
        }
        do {
            if try GrammarLawTransformer.transformedBaseline(for: witness) != witness.candidate {
                violations.append("candidate is not the declared transformation")
            }
        } catch {
            violations.append(String(describing: error))
        }
        return .init(
            witnessID: witness.id, law: witness.law,
            passed: violations.isEmpty, violations: violations
        )
    }

    public static func requireValid(_ witness: GrammarLawWitness) throws {
        guard !witness.id.isEmpty else { throw GrammarLawError.emptyIdentity }
        let evaluation = evaluate(witness)
        guard evaluation.passed else {
            throw GrammarLawError.malformedWitness(evaluation.violations)
        }
    }
}
