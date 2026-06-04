import Testing
@testable import Grammar

// MARK: - Production tests

@Test func production_isFinal_allTerminals() {
    let p = Production(goal: "A", rule: [t("a"), t("b")])
    #expect(p.isFinal == true)
}

@Test func production_isFinal_mixedSymbols() {
    let p = Production(goal: "A", rule: [t("a"), n("B")])
    #expect(p.isFinal == false)
}

@Test func production_isFinal_emptyRule() {
    let p = Production(goal: "A", rule: [])
    #expect(p.isFinal == true)   // vacuously all satisfy
}

@Test func production_isNullable_epsilonTerminal() {
    let p = Production(goal: "A", rule: [Symbol.terminal(.meta(.eps))])
    #expect(p.isNullable == true)
}

@Test func production_isNullable_emptyStringTerminal() {
    let p = Production(goal: "A", rule: [t("")])
    #expect(p.isNullable == true)
}

@Test func production_isNullable_nonTerminal() {
    let p = Production(goal: "A", rule: [n("B")])
    #expect(p.isNullable == false)
}

@Test func production_isInChomskyNormalForm_unitTerminal() {
    let p = Production(goal: "A", rule: [t("a")])
    #expect(p.isInChomskyNormalForm == true)
}

@Test func production_isInChomskyNormalForm_twoNonTerminals() {
    let p = Production(goal: "A", rule: [n("B"), n("C")])
    #expect(p.isInChomskyNormalForm == true)
}

@Test func production_isInChomskyNormalForm_longRule() {
    let p = Production(goal: "A", rule: [n("B"), n("C"), n("D")])
    #expect(p.isInChomskyNormalForm == false)
}

@Test func production_isInChomskyNormalForm_twoTerminals() {
    let p = Production(goal: "A", rule: [t("a"), t("b")])
    #expect(p.isInChomskyNormalForm == false)
}

@Test func production_generatedTerminals() {
    let p = Production(goal: "A", rule: [t("a"), n("B"), t("c")])
    let terminals = p.generatedTerminals
    #expect(terminals.count == 2)
    #expect(terminals.contains(Terminal(string: "a")))
    #expect(terminals.contains(Terminal(string: "c")))
}

@Test func production_generatedNonTerminals() {
    let p = Production(goal: "A", rule: [t("a"), n("B"), n("C")])
    let nts = p.generatedNonTerminals
    #expect(nts.count == 2)
    #expect(nts.contains(NonTerminal(name: "B")))
    #expect(nts.contains(NonTerminal(name: "C")))
}

@Test func production_containsSymbol_found() {
    let p = Production(goal: "A", rule: [t("a"), n("B"), t("c")])
    let result = p.containsSymbol(n("B"))
    #expect(result?.match == true)
    #expect(result?.position == 1)
}

@Test func production_containsSymbol_notFound() {
    let p = Production(goal: "A", rule: [t("a"), t("b")])
    let result = p.containsSymbol(n("B"))
    #expect(result == nil)
}

@Test func production_equality() {
    let p1 = Production(goal: "A", rule: [t("a"), n("B")])
    let p2 = Production(goal: "A", rule: [t("a"), n("B")])
    let p3 = Production(goal: "A", rule: [t("b")])
    #expect(p1 == p2)
    #expect(p1 != p3)
}

@Test func production_description() {
    let p = Production(goal: "E", rule: [n("E"), t("+"), n("T")])
    let desc = p.description
    #expect(desc.contains("E"))
    #expect(desc.contains("+"))
    #expect(desc.contains("T"))
}
