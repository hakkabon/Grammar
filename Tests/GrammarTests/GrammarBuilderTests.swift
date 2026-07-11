import Testing
@testable import Grammar

// MARK: - Plain concatenation

@Test func rule_plainConcatenation_producesOneFlatProduction() {
    let rules = [Rule("A") { t("x"); t("y") }]

    let (productions, generated) = RuleNotation().rewrite(rules)

    #expect(productions == [Production(goal: "A", rule: [t("x"), t("y")])])
    #expect(generated.isEmpty)
}

@Test func rule_emptyBody_producesEpsilonProduction() {
    let rules = [Rule("A") {}]

    let (productions, _) = RuleNotation().rewrite(rules)

    #expect(productions.count == 1)
    #expect(productions.first?.rule.isEmpty == true)
}

// MARK: - Top-level alternation: no synthetic non-terminal needed

@Test func rule_topLevelAlternation_producesOneProductionPerBranch_noSyntheticNonTerminal() {
    let rules = [Rule("A") { Alt { t("x"); t("y"); t("z") } }]

    let (productions, generated) = RuleNotation().rewrite(rules)

    #expect(productions.count == 3)
    #expect(productions.map(\.goal).allSatisfy { $0 == NonTerminal(name: "A") })
    #expect(productions.map(\.rule) == [[t("x")], [t("y")], [t("z")]])
    #expect(generated.isEmpty) // "A" itself already serves as the choice point
}

// MARK: - Nested alternation: synthetic non-terminal required

@Test func rule_nestedAlternation_generatesSyntheticNonTerminal() throws {
    let rules = [Rule("A") { t("x"); Alt { t("y"); t("z") } }]

    let (productions, generated) = RuleNotation().rewrite(rules)

    #expect(generated.count == 1)
    let auxGoal = try #require(generated.first)
    #expect(auxGoal.name.hasPrefix("@alt_"))

    let aProduction = try #require(productions.first { $0.goal == NonTerminal(name: "A") })
    #expect(aProduction.rule == [t("x"), .nonTerminal(auxGoal)])

    let auxProductions = productions.filter { $0.goal == auxGoal }
    #expect(auxProductions.map(\.rule) == [[t("y")], [t("z")]])
}

// MARK: - Optional

@Test func rule_optional_generatesSyntheticNonTerminalWithEpsilonBranch() throws {
    let rules = [Rule("A") { t("x"); Opt { t("y") } }]

    let (productions, generated) = RuleNotation().rewrite(rules)

    let auxGoal = try #require(generated.first)
    #expect(auxGoal.name.hasPrefix("@opt_"))

    let aProduction = try #require(productions.first { $0.goal == NonTerminal(name: "A") })
    #expect(aProduction.rule == [t("x"), .nonTerminal(auxGoal)])

    let auxProductions = productions.filter { $0.goal == auxGoal }.map(\.rule)
    #expect(auxProductions.contains([t("y")]))
    #expect(auxProductions.contains([])) // the epsilon branch
}

// MARK: - Repetition (zero or more)

@Test func rule_repetition_generatesRightRecursiveSyntheticNonTerminal() throws {
    let rules = [Rule("A") { t("x"); Seq { t("y") } }]

    let (productions, generated) = RuleNotation().rewrite(rules)

    let auxGoal = try #require(generated.first)
    #expect(auxGoal.name.hasPrefix("@rep_"))

    let auxProductions = productions.filter { $0.goal == auxGoal }.map(\.rule)
    #expect(auxProductions.contains([t("y"), .nonTerminal(auxGoal)])) // recursive branch
    #expect(auxProductions.contains([]))                              // terminating branch
}

// MARK: - Grouping is transparent: it never introduces its own synthetic non-terminal

@Test func rule_groupingAroundPlainConcatenation_isTransparent() {
    let rules = [Rule("A") { Grp { t("x"); t("y") } }]

    let (productions, generated) = RuleNotation().rewrite(rules)

    #expect(productions == [Production(goal: "A", rule: [t("x"), t("y")])])
    #expect(generated.isEmpty)
}

// MARK: - Rules never need to appear in dependency order

// Unlike the text-based notations (BNF/EBNF/WSN/generic), where `<Identifier>`
// is just a string until `StandardNotation` resolves it, the DSL's `n(_:)`
// already produces a fully-formed `Symbol.nonTerminal` at the call site — so
// there is no lookup table to populate first, and declaration order between
// rules was never able to matter here. This test exists mainly as documentation
// of that guarantee.
@Test func rules_referencingEachOther_resolveRegardlessOfDeclarationOrder() {
    let rules = [
        Rule("A") { n("B") },
        Rule("B") { t("x") },
    ]

    let (productions, _) = RuleNotation().rewrite(rules)

    let aProduction = productions.first { $0.goal == NonTerminal(name: "A") }
    #expect(aProduction?.rule == [n("B")])
}

// MARK: - lt(_:) / ct(_:) helpers (parity with Terminal.stringList / .characterRange)

@Test func lt_buildsAStringListTerminal() {
    let rules = [Rule("Bool") { lt("true", "false") }]

    let (productions, _) = RuleNotation().rewrite(rules)

    #expect(productions.first?.rule == [.terminal(Terminal(list: ["true", "false"]))])
}

@Test func ct_buildsACharacterRangeTerminal() {
    let rules = [Rule("Digit") { ct("0" ... "9") }]

    let (productions, _) = RuleNotation().rewrite(rules)

    #expect(productions.first?.rule == [.terminal(Terminal(range: "0" ... "9"))])
}

// MARK: - End-to-end via Grammar(start:builder:) — regression guard

// Before this patch, `Grammar(start:builder:)` discarded the built rules
// entirely and returned `Grammar(productions: [], start: "", lexicalTokens: [:])`
// no matter what was written in the closure. These two checks exist
// specifically to catch that regression if it ever comes back.
@Test func grammarFromDSL_isNotEmpty_andHasTheDeclaredStartSymbol() {
    let grammar = Grammar(start: "A") {
        Rule("A") { Alt { t("x"); Cat { t("x"); n("B") } } }
        Rule("B") { t("y") }
    }

    #expect(grammar.start == NonTerminal(name: "A"))
    #expect(grammar.productions.isEmpty == false)
    #expect(grammar.productions.count == 3) // two branches for A, one for B
}
