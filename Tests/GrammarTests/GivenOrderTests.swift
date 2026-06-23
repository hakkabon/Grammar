import Testing
@testable import Grammar

// MARK: - Grammar.givenOrder(productionOrder:) tests

@Test func givenOrder_sortsGroupsAccordingToExplicitOrder() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "S", lexicalTokens: [:])

    let result = grammar.givenOrder(productionOrder: ["B", "S", "A"])

    #expect(result.map { $0.0 } == ["B", "S", "A"].map { NonTerminal(name: $0) })
}

@Test func givenOrder_keepsAllProductionsForAGoalTogether() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [t("a")]),
        Production(goal: "S", rule: [t("b")]),
        Production(goal: "S", rule: [t("c")]),
        Production(goal: "A", rule: [t("x")]),
    ], start: "S", lexicalTokens: [:])

    let result = grammar.givenOrder(productionOrder: ["A", "S"])

    let sGroup = result.first { $0.0 == NonTerminal(name: "S") }
    #expect(sGroup?.1.count == 3)
}

@Test func givenOrder_preservesTotalProductionCount() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "A", rule: [t("a2")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "S", lexicalTokens: [:])

    let result = grammar.givenOrder(productionOrder: ["B", "A", "S"])

    let total = result.reduce(0) { $0 + $1.1.count }
    #expect(total == grammar.productions.count)
}

@Test func givenOrder_unmentionedGoalsAreAppendedAfterOrderedOnes() {
    // Only "B" is given an explicit position; "A" and "C" are unmentioned
    // and should keep their original relative (first-appearance) order,
    // placed after "B".
    let grammar = Grammar(productions: [
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
        Production(goal: "C", rule: [t("c")]),
    ], start: "A", lexicalTokens: [:])

    let result = grammar.givenOrder(productionOrder: ["B"])

    #expect(result.map { $0.0 } == ["B", "A", "C"].map { NonTerminal(name: $0) })
}

@Test func givenOrder_emptyOrderFallsBackToFirstAppearanceOrder() {
    let grammar = Grammar(productions: [
        Production(goal: "C", rule: [t("c")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "C", lexicalTokens: [:])

    let result = grammar.givenOrder(productionOrder: [])

    #expect(result.map { $0.0 } == ["C", "A", "B"].map { NonTerminal(name: $0) })
}

@Test func givenOrder_generatedVariantsSortByBaseName() {
    // "S-1" is a generated variant of "S" and should sort to S's position,
    // even though only "S" (not "S-1") appears in the explicit order.
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [t("s")]),
        Production(goal: "S-1", rule: [t("s1")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "S", lexicalTokens: [:])

    let result = grammar.givenOrder(productionOrder: ["A", "S", "B"])

    #expect(result.map { $0.0 } == ["A", "S", "S-1", "B"].map { NonTerminal(name: $0) })
}

@Test func givenOrder_duplicateNamesInOrderAreIgnored() {
    let grammar = Grammar(productions: [
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "A", lexicalTokens: [:])

    let withDuplicates = grammar.givenOrder(productionOrder: ["B", "B", "A", "A"])
    let withoutDuplicates = grammar.givenOrder(productionOrder: ["B", "A"])

    #expect(withDuplicates.map { $0.0 } == withoutDuplicates.map { $0.0 })
    #expect(withDuplicates.map { $0.0 } == ["B", "A"].map { NonTerminal(name: $0) })
}

@Test func givenOrder_namesNotPresentInGrammarAreHarmless() {
    let grammar = Grammar(productions: [
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "A", lexicalTokens: [:])

    let result = grammar.givenOrder(productionOrder: ["Z", "B", "Y", "A"])

    // Only the grammar's actual goals should appear in the result.
    #expect(result.map { $0.0 } == ["B", "A"].map { NonTerminal(name: $0) })
}

@Test func givenOrder_resultContainsEachGoalExactlyOnce() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "A", rule: [t("a2")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "S", lexicalTokens: [:])

    let result = grammar.givenOrder(productionOrder: ["A", "S", "B"])

    #expect(result.count == 3)
    #expect(Set(result.map { $0.0 }) == grammar.nonTerminals)
}

@Test func givenOrder_singleGoalGrammarIsUnaffectedByOrder() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [t("a")]),
        Production(goal: "S", rule: [t("b")]),
    ], start: "S", lexicalTokens: [:])

    let result = grammar.givenOrder(productionOrder: ["irrelevant", "names"])

    #expect(result.count == 1)
    #expect(result.first?.0 == NonTerminal(name: "S"))
    #expect(result.first?.1.count == 2)
}
