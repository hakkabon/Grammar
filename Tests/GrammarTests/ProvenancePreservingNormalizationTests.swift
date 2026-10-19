import Foundation
import Testing
@testable import Grammar

@Test func normalizationReportSchemaPublishesTheCurrentInterchangeVersion() throws {
    let root = URL(fileURLWithPath: #filePath)
        .deletingLastPathComponent().deletingLastPathComponent().deletingLastPathComponent()
    let data = try Data(contentsOf: root.appendingPathComponent("Schemas/NormalizationReport.schema.json"))
    let schema = try #require(JSONSerialization.jsonObject(with: data) as? [String: Any])
    let properties = try #require(schema["properties"] as? [String: Any])
    let version = try #require(properties["schemaVersion"] as? [String: Any])
    #expect(version["const"] as? Int == GrammarNormalizationReport.currentSchemaVersion)
}

@Test func chomskyNormalizationPreservesTotalDeterministicProvenance() throws {
    let grammar = try Grammar(
        wsn: "S : A B C | 'x'\nA : ε | 'a'\nB : D\nD : 'b'\nC : 'c'",
        start: "S"
    )
    let ids = grammar.productions.indices.map {
        GrammarProductionID(rawValue: "source-\($0 + 1)")
    }

    let first = try grammar.normalizationReport(to: .chomsky, productionIDs: ids)
    let second = try grammar.normalizationReport(to: .chomsky, productionIDs: ids)

    #expect(first == second)
    #expect(first.target == .chomsky)
    #expect(first.output.productions.count == first.provenance.count)
    #expect(first.preservesCompleteProvenance)
    #expect(first.provenance.contains { $0.kind == .synthetic })
    let syntheticLHS = Set(first.output.productions.compactMap { production in
        first.provenance.first { $0.outputProductionID == production.id }?.kind == .synthetic
            ? production.lhs : nil
    })
    #expect(syntheticLHS.isSubset(of: Set(first.output.generatedNonterminals)))
    #expect(first.provenance.allSatisfy { Set($0.sourceProductionIDs).isSubset(of: Set(ids)) })
    #expect(try JSONDecoder().decode(
        GrammarNormalizationReport.self,
        from: JSONEncoder().encode(first)
    ) == first)
}

@Test func normalizationRejectsAmbiguousSourceIdentities() throws {
    let grammar = Grammar(
        productions: [
            Production(goal: "S", rule: [t("a")]),
            Production(goal: "S", rule: [t("b")]),
        ],
        start: "S",
        lexicalTokens: [:]
    )
    let duplicate = GrammarProductionID(rawValue: "same")

    #expect(throws: GrammarNormalizationError.duplicateProductionIdentity(duplicate)) {
        try grammar.normalizationReport(to: .chomsky, productionIDs: [duplicate, duplicate])
    }
}

@Test func normalizationReportDecodingFailsClosed() throws {
    let grammar = Grammar(
        productions: [Production(goal: "S", rule: [t("a")])],
        start: "S",
        lexicalTokens: [:]
    )
    let report = try grammar.normalizationReport(to: .chomsky)
    var object = try #require(
        JSONSerialization.jsonObject(with: JSONEncoder().encode(report)) as? [String: Any]
    )
    object["schemaVersion"] = 2
    let unsupported = try JSONSerialization.data(withJSONObject: object)
    #expect(throws: GrammarNormalizationReportError.unsupportedSchemaVersion(2)) {
        try JSONDecoder().decode(GrammarNormalizationReport.self, from: unsupported)
    }

    object["schemaVersion"] = 1
    object["provenance"] = []
    let incomplete = try JSONSerialization.data(withJSONObject: object)
    #expect(throws: GrammarNormalizationReportError.invalidProvenance) {
        try JSONDecoder().decode(GrammarNormalizationReport.self, from: incomplete)
    }
}

@Test func preservedProductionsRetainExactIdentityEvidence() throws {
    let grammar = Grammar(
        productions: [
            Production(goal: "S", rule: [n("A"), n("B")]),
            Production(goal: "A", rule: [t("a")]),
            Production(goal: "B", rule: [t("b")]),
        ],
        start: "S",
        lexicalTokens: [:]
    )
    let report = try grammar.normalizationReport(to: .chomsky)

    #expect(report.preservesCompleteProvenance)
    #expect(report.provenance.allSatisfy { $0.precision == .exact })
    #expect(Set(report.provenance.map(\.sourceProductionIDs)) == Set([
        [GrammarProductionID(rawValue: "p1")],
        [GrammarProductionID(rawValue: "p2")],
        [GrammarProductionID(rawValue: "p3")],
    ]))
}

@Test func greibachNormalizationLabelsDerivedAndSyntheticAncestryTruthfully() throws {
    let grammar = try Grammar(wsn: "S : S 'a' | A 'b'\nA : 'c'", start: "S")
    let report = try grammar.normalizationReport(to: .greibach)

    #expect(report.preservesCompleteProvenance)
    #expect(report.appliedStages.contains(.leftRecursionElimination))
    #expect(report.appliedStages.contains(.leadingNonterminalExpansion))
    #expect(report.provenance.contains { $0.precision == .conservative })
    #expect(!report.output.productions.isEmpty)
}

@Test func grammarFormStateAndNormalizationReportShareTheSamePipeline() throws {
    var grammar = try Grammar(wsn: "S : 'a' S 'b' | 'a' 'b'", start: "S")
    let report = try grammar.normalizationReport(to: .chomsky)

    grammar.grammarForm = .chomsky
    let stateModel = try grammar.normalizedModel(
        productionIDs: grammar.productions.indices.map {
            GrammarProductionID(rawValue: "n\($0 + 1)")
        }
    )

    #expect(stateModel == report.output)
}

@Test func grammarFormRetainsExistingGeneratedNonterminalIdentities() throws {
    let existing = NonTerminal(name: "ExistingSynthetic")
    var grammar = Grammar(
        productions: [Production(goal: "S", rule: [t("a"), t("b")])],
        start: "S",
        empty: .eps,
        lexicalTokens: [:],
        generatedNonTerminals: [existing]
    )

    grammar.grammarForm = .chomsky

    #expect(grammar.generatedNonTerminals.contains(existing))
    #expect(try grammar.normalizationReport(to: .chomsky).preservesCompleteProvenance)
}

@Test func normalizationNeverCollidesWithUserNonterminalNames() throws {
    let grammar = Grammar(
        productions: [
            Production(goal: "S", rule: [t("a"), n("T0"), n("Y1")]),
            Production(goal: "T0", rule: [t("user-t")]),
            Production(goal: "Y1", rule: [t("user-y")]),
        ],
        start: "S",
        lexicalTokens: [:]
    )

    let report = try grammar.normalizationReport(to: .chomsky)
    let t0 = report.output.productions.first { $0.lhs == "T0" }
    let y1 = report.output.productions.first { $0.lhs == "Y1" }

    #expect(t0?.rhs == [.terminal(.literal("user-t"))])
    #expect(y1?.rhs == [.terminal(.literal("user-y"))])
    #expect(report.preservesCompleteProvenance)
}
