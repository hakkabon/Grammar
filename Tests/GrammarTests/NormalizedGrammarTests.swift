import Foundation
import Testing
@testable import Grammar

private let identifier = GrammarNormalizedTerminal.regularExpression("[A-Za-z_][A-Za-z0-9_]*")
private let plus = GrammarNormalizedTerminal.literal("+")

@Test func normalizedModelPreservesTerminalKindsOrderAndProvidedIdentities() throws {
    let grammar = Grammar(
        productions: [
            Production(goal: "Expression", rule: [n("Expression"), t("+"), n("Name")]),
            Production(goal: "Expression", rule: [n("Name")]),
            Production(goal: "Name", rule: [try rt("[A-Za-z_][A-Za-z0-9_]*")]),
        ],
        start: "Expression",
        lexicalTokens: ["identifier": try Terminal(expression: "[A-Za-z_][A-Za-z0-9_]*")]
    )
    let ids: [GrammarProductionID] = ["expression-add", "expression-name", "name-identifier"]
        .map(GrammarProductionID.init(rawValue:))

    let model = try grammar.normalizedModel(productionIDs: ids)

    #expect(model.schemaVersion == 1)
    #expect(model.productions.map(\.id) == ids)
    #expect(model.productions[0].rhs == [
        .nonterminal("Expression"), .terminal(plus), .nonterminal("Name")
    ])
    #expect(model.productions[2].rhs == [.terminal(identifier)])
    #expect(model.lexicalDefinitions == [
        GrammarLexicalDefinition(name: "identifier", terminal: identifier)
    ])

    let data = try JSONEncoder().encode(model)
    #expect(try JSONDecoder().decode(GrammarNormalizedModel.self, from: data) == model)
    let object = try #require(JSONSerialization.jsonObject(with: data) as? [String: Any])
    let productions = try #require(object["productions"] as? [[String: Any]])
    #expect(productions[0]["id"] as? String == "expression-add")
    let symbols = try #require(productions[0]["rhs"] as? [[String: Any]])
    #expect(symbols[0]["kind"] as? String == "nonterminal")
    #expect(symbols[1]["kind"] as? String == "terminal")
}

@Test func normalizedModelAssignsReproducibleOccurrenceIdentitiesAndPreservesDuplicates() throws {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [t("a")]),
        Production(goal: "S", rule: [t("a")]),
    ], start: "S", lexicalTokens: [:])

    let first = try grammar.normalizedModel()
    let second = try grammar.normalizedModel()

    #expect(first == second)
    #expect(first.productions.map(\.id.rawValue) == ["p1", "p2"])
    #expect(first.productions.count == 2)
    #expect(first.analyze().duplicateProductions.first?.productionIDs.map(\.rawValue) == ["p1", "p2"])
}

@Test func normalizedAnalysisIsCompleteDeterministicAndPredictive() throws {
    let model = try GrammarNormalizedModel(
        startSymbol: "S",
        productions: [
            .init(id: .init(rawValue: "s-ab"), lhs: "S", rhs: [.nonterminal("A"), .nonterminal("B")]),
            .init(id: .init(rawValue: "s-a"), lhs: "S", rhs: [.terminal(.literal("a"))]),
            .init(id: .init(rawValue: "a-a"), lhs: "A", rhs: [.terminal(.literal("a"))]),
            .init(id: .init(rawValue: "a-empty"), lhs: "A", rhs: []),
            .init(id: .init(rawValue: "b-b"), lhs: "B", rhs: [.terminal(.literal("b"))]),
            .init(id: .init(rawValue: "dead-loop"), lhs: "Dead", rhs: [.nonterminal("Dead")]),
            .init(id: .init(rawValue: "missing"), lhs: "MissingUser", rhs: [.nonterminal("Undefined")]),
        ],
        lexicalDefinitions: [
            .init(name: "A-token", terminal: .literal("a")),
            .init(name: "unused-token", terminal: .literal("unused")),
        ],
        precedence: [
            .init(level: 2, associativity: .left, terminals: [.literal("*")]),
            .init(level: 1, associativity: .left, terminals: [.literal("+")]),
        ]
    )

    let analysis = model.analyze()

    #expect(analysis.definedNonterminals == ["A", "B", "Dead", "MissingUser", "S"])
    #expect(analysis.undefinedNonterminals == ["Undefined"])
    #expect(analysis.reachableNonterminals == ["A", "B", "S"])
    #expect(analysis.unreachableNonterminals == ["Dead", "MissingUser"])
    #expect(analysis.productiveNonterminals == ["A", "B", "S"])
    #expect(analysis.unproductiveNonterminals == ["Dead", "MissingUser"])
    #expect(analysis.nullableNonterminals == ["A"])
    #expect(analysis.directlyLeftRecursiveNonterminals == ["Dead"])
    #expect(analysis.recursiveComponents == [["Dead"]])
    #expect(analysis.unusedLexicalDefinitions == ["unused-token"])
    #expect(model.precedence.map(\.level) == [1, 2])
    #expect(analysis.dependencies.contains(.init(from: "S", to: "A")))
    #expect(analysis.dependencies.contains(.init(from: "MissingUser", to: "Undefined")))

    let firstS = analysis.first.first { $0.nonterminal == "S" }?.lookaheads
    let followA = analysis.follow.first { $0.nonterminal == "A" }?.lookaheads
    #expect(firstS == [.terminal(.literal("a")), .terminal(.literal("b"))])
    #expect(followA == [.terminal(.literal("b"))])
    #expect(analysis.predictiveConflicts.count == 1)
    #expect(analysis.predictiveConflicts[0].nonterminal == "S")
    #expect(analysis.predictiveConflicts[0].lookaheads == [.terminal(.literal("a"))])
    #expect(!analysis.isLL1)

    let encoder = JSONEncoder()
    encoder.outputFormatting = [.sortedKeys]
    let encodedOnce = try encoder.encode(analysis)
    let encodedTwice = try encoder.encode(model.analyze())
    #expect(encodedOnce == encodedTwice)
}

@Test func normalizedModelRejectsInvalidIdentityAndUnloweredMetaSymbols() throws {
    let duplicate = GrammarProductionID(rawValue: "same")
    #expect(throws: GrammarNormalizationError.duplicateProductionIdentity(duplicate)) {
        try GrammarNormalizedModel(
            startSymbol: "S",
            productions: [
                .init(id: duplicate, lhs: "S", rhs: []),
                .init(id: duplicate, lhs: "S", rhs: [.terminal(.literal("a"))]),
            ]
        )
    }
    #expect(throws: GrammarNormalizationError.emptyProductionIdentity) {
        try GrammarNormalizedModel(
            startSymbol: "S",
            productions: [.init(id: .init(rawValue: ""), lhs: "S", rhs: [])]
        )
    }
    #expect(throws: GrammarNormalizationError.epsilonTerminal(
        production: .init(rawValue: "explicit-empty")
    )) {
        try GrammarNormalizedModel(
            startSymbol: "S",
            productions: [
                .init(id: .init(rawValue: "explicit-empty"), lhs: "S", rhs: [.terminal(.literal(""))])
            ]
        )
    }

    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [.metaSymbol(.lbrace)])
    ], start: "S", lexicalTokens: [:])
    #expect(throws: GrammarNormalizationError.metaSymbol(
        production: .init(rawValue: "p1"), symbol: "{"
    )) {
        try grammar.normalizedModel()
    }
}

@Test func normalizedGrammarSchemaPublishesTheCurrentInterchangeVersion() throws {
    let root = URL(fileURLWithPath: #filePath)
        .deletingLastPathComponent().deletingLastPathComponent().deletingLastPathComponent()
    let data = try Data(contentsOf: root.appendingPathComponent("Schemas/NormalizedGrammar.schema.json"))
    let schema = try #require(JSONSerialization.jsonObject(with: data) as? [String: Any])
    let properties = try #require(schema["properties"] as? [String: Any])
    let version = try #require(properties["schemaVersion"] as? [String: Any])
    #expect(version["const"] as? Int == GrammarNormalizedModel.currentSchemaVersion)
}
