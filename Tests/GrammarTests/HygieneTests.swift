import Testing
@testable import Grammar

// MARK: - Grammar hygiene tests

@Test func hygiene_undefinedNonterminals_found() {
    // B is referenced but has no production
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B")]),
        Production(goal: "A", rule: [t("a")]),
        // no production for B
    ], start: "S", lexicalTokens: [:])
    
    let undefined = grammar.undefinedNonterminals
    #expect(undefined.contains(NonTerminal(name: "B")))
}

@Test func hygiene_undefinedNonterminals_noneWhenComplete() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A")]),
        Production(goal: "A", rule: [t("a")]),
    ], start: "S", lexicalTokens: [:])
    
    let undefined = grammar.undefinedNonterminals
    #expect(undefined.isEmpty)
}

@Test func hygiene_eliminateUnusedProductions_removesUnreachable() {
    // Z is defined but never reachable from S
    let productions = [
        Production(goal: "S", rule: [n("A")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "Z", rule: [t("z")]),   // unreachable
    ]
    
    let reachable = Grammar.eliminateUnusedProductions(productions: productions, start: "S")
    let goals = Set(reachable.map { $0.goal })
    #expect(!goals.contains(NonTerminal(name: "Z")))
    #expect(goals.contains(NonTerminal(name: "S")))
    #expect(goals.contains(NonTerminal(name: "A")))
}

@Test func hygiene_eliminateUnusedProductions_keepsAllReachable() {
    let productions = [
        Production(goal: "S", rule: [n("A"), n("B")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
    ]
    
    let reachable = Grammar.eliminateUnusedProductions(productions: productions, start: "S")
    #expect(reachable.count == 3)
}

@Test func hygiene_eliminateUnitRules_chainsAreCollapsed() {
    // S → A, A → B, B → "b"
    let productions = [
        Production(goal: "S", rule: [n("A")]),
        Production(goal: "A", rule: [n("B")]),
        Production(goal: "B", rule: [t("b")]),
    ]
    
    let result = Grammar.eliminateUnitRules(productions: productions)
    // All chains should be resolved to terminal productions
    let terminalProds = result.filter { $0.isFinal }
    #expect(!terminalProds.isEmpty)
    // S should eventually derive "b"
    let sDerivesB = terminalProds.contains { $0.goal == NonTerminal(name: "S") && $0.rule == [t("b")] }
    #expect(sDerivesB)
}

@Test func hygiene_eliminateEmpty_removesEpsilonFromMiddle() async throws {
    // S → A B, A → ε  ⟹  S → B should be added
    let grammar = try Grammar(wsn: """
        S : A B
        A : ε
        B : 'b'
    """, start: "S")
    
    let result = Grammar.eliminateEmpty(productions: grammar.productions, start: grammar.start)
    // After elimination, should have S → B (without A)
    let sBonly = result.contains { $0.goal == NonTerminal(name: "S") && $0.rule == [n("B")] }
    #expect(sBonly)
}

@Test func hygiene_unreachableNonTerminals() async throws {
    // Z is unreachable from S
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "Z", rule: [t("z")]),
    ], start: "S", lexicalTokens: [:])
    
    let unreachable = grammar.unreachableNonTerminals
    #expect(unreachable.contains(NonTerminal(name: "Z")))
    #expect(!unreachable.contains(NonTerminal(name: "S")))
    #expect(!unreachable.contains(NonTerminal(name: "A")))
}

// MARK: - Nullable tests

@Test func nullable_allNullableNonTerminals_directEps() async throws {
    let grammar = try Grammar(wsn: """
        A : ε
        B : 'b'
    """, start: "A")
    
    let nullables = grammar.allNullableNonTerminals()
    #expect(nullables.contains(NonTerminal(name: "A")))
    #expect(!nullables.contains(NonTerminal(name: "B")))
}

@Test func nullable_allNullableNonTerminals_indirect() async throws {
    let grammar = try Grammar(wsn: """
        S : A B
        A : ε
        B : ε
    """, start: "S")
    
    let nullables = grammar.allNullableNonTerminals()
    #expect(nullables.contains(NonTerminal(name: "S")))
    #expect(nullables.contains(NonTerminal(name: "A")))
    #expect(nullables.contains(NonTerminal(name: "B")))
}

@Test func nullable_isNullable_nonTerminal() async throws {
    let grammar = try Grammar(wsn: """
        A : ε
        B : 'b'
    """, start: "A")
    
    #expect(grammar.isNullable(NonTerminal(name: "A")) == true)
    #expect(grammar.isNullable(NonTerminal(name: "B")) == false)
}

@Test func nullable_isNullable_symbolSequence() async throws {
    let grammar = try Grammar(wsn: """
        A : ε
        B : 'b'
        S : A B
    """, start: "S")
    
    // Sequence [A] where A is nullable
    #expect(grammar.isNullable([n("A")]) == true)
    // Sequence [B] where B is not nullable
    #expect(grammar.isNullable([n("B")]) == false)
    // Mixed: not nullable because B is not nullable
    #expect(grammar.isNullable([n("A"), n("B")]) == false)
}

// MARK: - Cycle Detection tests

@Test func cycleDetection_noCycle_linearGrammar() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A")]),
        Production(goal: "A", rule: [t("a")]),
    ], start: "S", lexicalTokens: [:])
    
    let cycles = grammar.detectCycles()
    #expect(cycles.isEmpty)
}

@Test func cycleDetection_directCycle() {
    // S → A, A → A  (direct cycle)
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A")]),
        Production(goal: "A", rule: [n("A")]),
    ], start: "S", lexicalTokens: [:])
    
    let cycles = grammar.detectCycles()
    #expect(!cycles.isEmpty)
}

@Test func cycleDetection_indirectCycle() async throws {
    let grammar = try Grammar(wsn: """
        S : A
        A : B
        B : C
        C : A
    """, start: "S")
    let (prods, _) = grammar.rewriteToStandardForm()
    let standard = Grammar(productions: prods, start: grammar.start, lexicalTokens: [:])
    
    let cycles = standard.detectCycles()
    #expect(!cycles.isEmpty)
}
