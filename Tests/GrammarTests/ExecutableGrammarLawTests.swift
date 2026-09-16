import Foundation
import Grammar
import Testing

private func lawModel() throws -> GrammarNormalizedModel {
    try GrammarNormalizedModel(
        startSymbol: "Expression",
        productions: [
            .init(
                id: .init(rawValue: "expression-add"), lhs: "Expression",
                rhs: [.nonterminal("Expression"), .terminal(.literal("+")), .nonterminal("Term")]
            ),
            .init(id: .init(rawValue: "expression-term"), lhs: "Expression", rhs: [.nonterminal("Term")]),
            .init(id: .init(rawValue: "term-number"), lhs: "Term", rhs: [.terminal(.literal("n"))]),
        ],
        lexicalDefinitions: [.init(name: "number", terminal: .literal("n"))],
        generatedNonterminals: ["Term"]
    )
}

@Test func productionPermutationProducesAValidatedSelfContainedWitness() throws {
    let model = try lawModel()
    let witness = try GrammarLawTransformer.permuteProductions(
        model,
        order: model.productions.map(\.id).reversed(),
        id: "production-order"
    )

    #expect(witness.law == .productionPermutation)
    #expect(witness.baseline.productions.map(\.id).reversed() == witness.candidate.productions.map(\.id))
    #expect(GrammarLawVerifier.evaluate(witness).passed)
    let data = try JSONEncoder().encode(witness)
    #expect(try JSONDecoder().decode(GrammarLawWitness.self, from: data) == witness)
}

@Test func alphaRenamingChangesEveryNonterminalReferenceButPreservesProductionIdentity() throws {
    let model = try lawModel()
    let witness = try GrammarLawTransformer.alphaRenameNonterminals(
        model,
        renames: [
            .init(from: "Expression", to: "Formula"),
            .init(from: "Term", to: "Atom"),
        ],
        id: "alpha-rename"
    )

    #expect(witness.candidate.startSymbol == "Formula")
    #expect(witness.candidate.productions.map(\.id) == model.productions.map(\.id))
    #expect(witness.candidate.generatedNonterminals == ["Atom"])
    #expect(witness.candidate.productions.allSatisfy { production in
        production.lhs != "Expression" && production.lhs != "Term"
            && !production.rhs.contains(.nonterminal("Expression"))
            && !production.rhs.contains(.nonterminal("Term"))
    })
    #expect(GrammarLawVerifier.evaluate(witness).passed)
}

@Test func invalidTransformationsAndTamperedWitnessesFailClosed() throws {
    let model = try lawModel()
    #expect(throws: GrammarLawError.self) {
        try GrammarLawTransformer.permuteProductions(
            model, order: model.productions.map(\.id), id: "unchanged"
        )
    }
    #expect(throws: GrammarLawError.self) {
        try GrammarLawTransformer.alphaRenameNonterminals(
            model,
            renames: [
                .init(from: "Expression", to: "Term"),
            ],
            id: "collision"
        )
    }

    let witness = try GrammarLawTransformer.permuteProductions(
        model, order: model.productions.map(\.id).reversed(), id: "future"
    )
    let encoded = try JSONEncoder().encode(witness)
    var object = try #require(JSONSerialization.jsonObject(with: encoded) as? [String: Any])
    object["schemaVersion"] = GrammarLawWitness.currentSchemaVersion + 1
    #expect(throws: GrammarLawError.self) {
        try JSONDecoder().decode(
            GrammarLawWitness.self, from: JSONSerialization.data(withJSONObject: object)
        )
    }
}

@Test func executableGrammarLawSchemaPublishesCurrentVersion() throws {
    let root = URL(fileURLWithPath: #filePath)
        .deletingLastPathComponent().deletingLastPathComponent().deletingLastPathComponent()
    let object = try #require(JSONSerialization.jsonObject(
        with: Data(contentsOf: root.appendingPathComponent("Schemas/ExecutableGrammarLaw.schema.json"))
    ) as? [String: Any])
    let properties = try #require(object["properties"] as? [String: Any])
    let version = try #require(properties["schemaVersion"] as? [String: Any])
    #expect(version["const"] as? Int == GrammarLawWitness.currentSchemaVersion)
}
