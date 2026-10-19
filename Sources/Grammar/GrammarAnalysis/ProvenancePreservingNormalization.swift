import Foundation

/// The individually observable stages in Grammar's normal-form pipelines.
public enum GrammarNormalizationStage: String, CaseIterable, Hashable, Codable, Sendable {
    case standardNotation
    case epsilonElimination
    case unitElimination
    case terminalIsolation
    case binarization
    case leftRecursionElimination
    case leadingNonterminalExpansion
    case tailTerminalIsolation
}

/// Whether an output rule is byte-for-byte structural ancestry or a safe
/// over-approximation of all source rules that may have contributed to it.
public enum GrammarProvenancePrecision: String, Hashable, Codable, Sendable {
    case exact
    case conservative
}

public enum GrammarNormalizedProductionKind: String, Hashable, Codable, Sendable {
    case preserved
    case derived
    case synthetic
}

public enum GrammarNormalizationReportError: Error, Equatable, Sendable {
    case unsupportedSchemaVersion(Int)
    case invalidProvenance
}

/// A source-side snapshot deliberately permits EBNF meta-symbols. The
/// parser-facing `GrammarNormalizedModel` cannot represent those symbols.
public struct GrammarNormalizationSourceProduction: Identifiable, Hashable, Codable, Sendable {
    public let id: GrammarProductionID
    public let lhs: String
    public let rhs: [String]

    public init(id: GrammarProductionID, lhs: String, rhs: [String]) {
        self.id = id
        self.lhs = lhs
        self.rhs = rhs
    }
}

/// Connects one emitted parser-facing production to its source ancestry.
/// Conservative ancestry is intentionally explicit: it contains the complete
/// reachable source closure and never presents an inferred one-to-one origin.
public struct GrammarProductionProvenance: Identifiable, Hashable, Codable, Sendable {
    public let outputProductionID: GrammarProductionID
    public let sourceProductionIDs: [GrammarProductionID]
    public let kind: GrammarNormalizedProductionKind
    public let precision: GrammarProvenancePrecision
    public var id: GrammarProductionID { outputProductionID }

    public init(
        outputProductionID: GrammarProductionID,
        sourceProductionIDs: [GrammarProductionID],
        kind: GrammarNormalizedProductionKind,
        precision: GrammarProvenancePrecision
    ) {
        self.outputProductionID = outputProductionID
        self.sourceProductionIDs = sourceProductionIDs.sorted()
        self.kind = kind
        self.precision = precision
    }
}

/// Versioned evidence for a normal-form rewrite. `output` is suitable for
/// parser construction; `provenance` is a total relation over its productions.
public struct GrammarNormalizationReport: Hashable, Codable, Sendable {
    public static let currentSchemaVersion = 1

    public let schemaVersion: Int
    public let target: Grammar.GrammarForm
    public let sourceProductions: [GrammarNormalizationSourceProduction]
    public let output: GrammarNormalizedModel
    public let appliedStages: [GrammarNormalizationStage]
    public let provenance: [GrammarProductionProvenance]

    public var preservesCompleteProvenance: Bool {
        let sourceIDs = sourceProductions.map(\.id)
        let outputIDs = output.productions.map(\.id)
        let evidenceIDs = provenance.map(\.outputProductionID)
        let knownSources = Set(sourceIDs)
        return schemaVersion == Self.currentSchemaVersion
            && knownSources.count == sourceIDs.count
            && Set(outputIDs).count == outputIDs.count
            && evidenceIDs.count == outputIDs.count
            && Set(evidenceIDs) == Set(outputIDs)
            && provenance.allSatisfy {
                !$0.sourceProductionIDs.isEmpty
                    && Set($0.sourceProductionIDs).count == $0.sourceProductionIDs.count
                    && Set($0.sourceProductionIDs).isSubset(of: knownSources)
            }
    }

    init(
        target: Grammar.GrammarForm,
        sourceProductions: [GrammarNormalizationSourceProduction],
        output: GrammarNormalizedModel,
        appliedStages: [GrammarNormalizationStage],
        provenance: [GrammarProductionProvenance]
    ) {
        schemaVersion = Self.currentSchemaVersion
        self.target = target
        self.sourceProductions = sourceProductions
        self.output = output
        self.appliedStages = appliedStages
        self.provenance = provenance
    }

    private enum CodingKeys: String, CodingKey {
        case schemaVersion, target, sourceProductions, output, appliedStages, provenance
    }

    public init(from decoder: Decoder) throws {
        let values = try decoder.container(keyedBy: CodingKeys.self)
        schemaVersion = try values.decode(Int.self, forKey: .schemaVersion)
        guard schemaVersion == Self.currentSchemaVersion else {
            throw GrammarNormalizationReportError.unsupportedSchemaVersion(schemaVersion)
        }
        target = try values.decode(Grammar.GrammarForm.self, forKey: .target)
        sourceProductions = try values.decode(
            [GrammarNormalizationSourceProduction].self, forKey: .sourceProductions
        )
        output = try values.decode(GrammarNormalizedModel.self, forKey: .output)
        appliedStages = try values.decode([GrammarNormalizationStage].self, forKey: .appliedStages)
        provenance = try values.decode([GrammarProductionProvenance].self, forKey: .provenance)
        guard preservesCompleteProvenance else {
            throw GrammarNormalizationReportError.invalidProvenance
        }
    }

    public func encode(to encoder: Encoder) throws {
        var values = encoder.container(keyedBy: CodingKeys.self)
        try values.encode(schemaVersion, forKey: .schemaVersion)
        try values.encode(target, forKey: .target)
        try values.encode(sourceProductions, forKey: .sourceProductions)
        try values.encode(output, forKey: .output)
        try values.encode(appliedStages, forKey: .appliedStages)
        try values.encode(provenance, forKey: .provenance)
    }
}

public extension Grammar {
    /// Rewrites the grammar while preserving a deterministic, total ancestry
    /// relation. Derived rules use a conservative source closure when a normal-
    /// form stage combines, removes, or shares intermediate productions.
    func normalizationReport(
        to target: GrammarForm,
        productionIDs: [GrammarProductionID]? = nil
    ) throws -> GrammarNormalizationReport {
        if let productionIDs, productionIDs.count != productions.count {
            throw GrammarNormalizationError.productionIdentityCount(
                expected: productions.count, actual: productionIDs.count
            )
        }
        let sourceIDs = productionIDs
            ?? productions.indices.map { GrammarProductionID(rawValue: "p\($0 + 1)") }
        var uniqueSourceIDs: Set<GrammarProductionID> = []
        for id in sourceIDs {
            guard !id.rawValue.isEmpty else {
                throw GrammarNormalizationError.emptyProductionIdentity
            }
            guard uniqueSourceIDs.insert(id).inserted else {
                throw GrammarNormalizationError.duplicateProductionIdentity(id)
            }
        }
        let source = zip(productions, sourceIDs).map { production, id in
            GrammarNormalizationSourceProduction(
                id: id,
                lhs: production.goal.name,
                rhs: production.rule.map(\.description)
            )
        }

        let transformed: Grammar
        let stages: [GrammarNormalizationStage]
        switch target {
        case .none:
            transformed = self
            stages = []
        case .standard:
            transformed = standardFormGrammar()
            stages = [.standardNotation]
        case .chomsky:
            transformed = standardFormGrammar().toChomskyNormalForm()
            stages = [
                .standardNotation, .epsilonElimination, .unitElimination,
                .terminalIsolation, .binarization,
            ]
        case .greibach:
            transformed = standardFormGrammar().toGreibachNormalForm()
            stages = [
                .standardNotation, .epsilonElimination, .unitElimination,
                .leftRecursionElimination, .leadingNonterminalExpansion,
                .tailTerminalIsolation,
            ]
        }

        let outputIDs = transformed.productions.indices.map {
            GrammarProductionID(rawValue: "n\($0 + 1)")
        }
        let output = try transformed.normalizedModel(productionIDs: outputIDs)
        let ancestry = provenance(
            sourceProductions: productions,
            sourceIDs: sourceIDs,
            outputProductions: transformed.productions,
            outputIDs: outputIDs
        )
        return GrammarNormalizationReport(
            target: target,
            sourceProductions: source,
            output: output,
            appliedStages: stages,
            provenance: ancestry
        )
    }

    private func standardFormGrammar() -> Grammar {
        let rewritten = rewriteToStandardForm()
        return Grammar(
            productions: rewritten.0,
            start: start,
            empty: epsilon,
            lexicalTokens: lexicalTokens,
            generatedNonTerminals: generatedNonTerminals.union(rewritten.1)
        )
    }

    private func provenance(
        sourceProductions: [Production],
        sourceIDs: [GrammarProductionID],
        outputProductions: [Production],
        outputIDs: [GrammarProductionID]
    ) -> [GrammarProductionProvenance] {
        let sourceNames = Set(sourceProductions.map { $0.goal.name })
        let sourcesByGoal = Dictionary(grouping: zip(sourceProductions, sourceIDs), by: {
            $0.0.goal.name
        })
        let sourceDependencies = Dictionary(grouping: sourceProductions, by: { $0.goal.name })
            .mapValues { productions in
                Set(productions.flatMap { $0.rule.compactMap(\.nonTerminal?.name) })
            }
        var outputParents: [String: Set<String>] = [:]
        for production in outputProductions {
            for child in production.rule.compactMap(\.nonTerminal?.name) {
                outputParents[child, default: []].insert(production.goal.name)
            }
        }

        func sourceClosure(from anchors: Set<String>) -> [GrammarProductionID] {
            var pending = anchors.sorted()
            var visited: Set<String> = []
            var result: Set<GrammarProductionID> = []
            while let name = pending.first {
                pending.removeFirst()
                guard visited.insert(name).inserted else { continue }
                result.formUnion(sourcesByGoal[name, default: []].map { $0.1 })
                pending.append(contentsOf: sourceDependencies[name, default: []].sorted())
            }
            return result.sorted()
        }

        func anchors(for goal: String) -> Set<String> {
            if sourceNames.contains(goal) { return [goal] }
            var pending = [goal]
            var visited: Set<String> = []
            var result: Set<String> = []
            while let name = pending.first {
                pending.removeFirst()
                guard visited.insert(name).inserted else { continue }
                for parent in outputParents[name, default: []].sorted() {
                    if sourceNames.contains(parent) { result.insert(parent) }
                    else { pending.append(parent) }
                }
            }
            return result
        }

        var exactOccurrences = Dictionary(
            grouping: zip(sourceProductions, sourceIDs),
            by: { $0.0 }
        ).mapValues { $0.map { $0.1 }.sorted() }
        var result: [GrammarProductionProvenance] = []
        for (production, outputID) in zip(outputProductions, outputIDs) {
            if let exact = exactOccurrences[production]?.first {
                exactOccurrences[production]?.removeFirst()
                result.append(GrammarProductionProvenance(
                    outputProductionID: outputID,
                    sourceProductionIDs: [exact],
                    kind: .preserved,
                    precision: .exact
                ))
                continue
            }
            let derivedAnchors = anchors(for: production.goal.name)
            let closure = sourceClosure(from: derivedAnchors)
            result.append(GrammarProductionProvenance(
                outputProductionID: outputID,
                sourceProductionIDs: closure.isEmpty ? sourceIDs : closure,
                kind: sourceNames.contains(production.goal.name) ? .derived : .synthetic,
                precision: .conservative
            ))
        }
        return result
    }
}
