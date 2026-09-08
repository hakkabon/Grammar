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
