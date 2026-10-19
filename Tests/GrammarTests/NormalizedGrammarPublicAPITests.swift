import Grammar
import Testing

@Test func normalizedGrammarContractIsUsableWithoutTestableImport() throws {
    let model = try GrammarNormalizedModel(
        startSymbol: "Expression",
        productions: [
            GrammarNormalizedProduction(
                id: GrammarProductionID(rawValue: "expression-name"),
                lhs: "Expression",
                rhs: [.nonterminal("Name")]
            ),
            GrammarNormalizedProduction(
                id: GrammarProductionID(rawValue: "name-identifier"),
                lhs: "Name",
                rhs: [.terminal(.regularExpression("[A-Za-z]+"))]
            ),
        ]
    )

    let analysis = model.analyze()
    #expect(analysis.isLL1)
    #expect(analysis.reachableNonterminals == ["Expression", "Name"])
}

@Test func normalizationProvenanceIsUsableWithoutTestableImport() throws {
    let grammar = Grammar(
        productions: [
            Production(
                goal: NonTerminal(name: "S"),
                rule: [.terminal(Terminal(string: "value"))]
            )
        ],
        start: NonTerminal(name: "S"),
        lexicalTokens: [:]
    )

    let report = try grammar.normalizationReport(to: .chomsky)
    #expect(report.schemaVersion == GrammarNormalizationReport.currentSchemaVersion)
    #expect(report.preservesCompleteProvenance)
    #expect(report.provenance.first?.precision == .exact)
}
