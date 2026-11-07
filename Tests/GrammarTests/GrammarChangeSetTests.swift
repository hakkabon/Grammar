import Grammar
import Testing

private func grammar(_ productions: [Production], lexical: LexicalSpecification = .empty)
    -> Grammar {
    var value = Grammar(productions: productions, start: "S", lexicalTokens: [:])
    value.lexicalSpecification = lexical
    return value
}

@Test func grammarChangeInvalidatesTransitiveProductionDependents() {
    let s: NonTerminal = "S", b: NonTerminal = "B", u: NonTerminal = "U"
    let old = grammar([
        .init(goal: s, rule: [.nonTerminal(b)]),
        .init(goal: b, rule: [.terminal("b")]),
        .init(goal: u, rule: [.terminal("u")]),
    ])
    let changed = grammar(old.productions + [
        .init(goal: b, rule: [.terminal("other")]),
    ])

    let delta = old.changeSet(to: changed)
    #expect(delta.affectedNonterminalNames == ["B", "S"])
    #expect(delta.invalidatedProductionIDSet.contains(GrammarProductionID(old.productions[0])))
    #expect(delta.invalidatedProductionIDSet.contains(GrammarProductionID(old.productions[1])))
    #expect(!delta.invalidatedProductionIDSet.contains(GrammarProductionID(old.productions[2])))
}

@Test func productionOrderDoesNotCreateAGrammarChange() {
    let productions = [
        Production(goal: "S", rule: [.terminal("a")]),
        Production(goal: "S", rule: [.terminal("b")]),
    ]
    let first = grammar(productions)
    let reordered = grammar(Array(productions.reversed()))

    #expect(first.changeSet(to: reordered).isEmpty)
    #expect(first.incrementalSemanticFingerprint == reordered.incrementalSemanticFingerprint)
}

@Test func lexicalChangeRequiresRetokenizationAndInvalidatesAllProductions() {
    let productions = [Production(goal: "S", rule: [.terminal("IDENTIFIER")])]
    let old = grammar(productions, lexical: .init(rules: [
        .init(name: "IDENTIFIER", matcher: .regularExpression("[a-z]+")),
    ]))
    let changed = grammar(productions, lexical: .init(rules: [
        .init(name: "IDENTIFIER", matcher: .regularExpression("[A-Za-z]+")),
    ]))

    let delta = old.changeSet(to: changed)
    #expect(delta.requiresRetokenization)
    #expect(delta.changedLexicalRuleNames == ["IDENTIFIER"])
    #expect(delta.invalidatedProductionIDs == [GrammarProductionID(productions[0])])
}
