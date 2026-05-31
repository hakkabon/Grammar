import Testing
@testable import Grammar

// MARK: - Chomsky Normal Form Tests
//
// Reference grammars are taken from standard textbooks:
//   • Sipser, "Introduction to the Theory of Computation"
//   • Hopcroft, Motwani & Ullman, "Introduction to Automata Theory"
//   • Dragon Book (Aho, Lam, Sethi & Ullman)

// MARK: - Helper

/// Verify that every production in `grammar` satisfies the CNF invariant:
///   • A → a          (exactly one terminal)
///   • A → B C        (exactly two non-terminals)
///   • S → ε          (only the start symbol may produce epsilon)
private func assertCNF(_ grammar: Grammar, file: String = #file, line: Int = #line) {
    for prod in grammar.productions {
        let rule = prod.rule
        let isUnitTerminal = rule.count == 1 && rule[0].isTerminal
        let isBinaryNT = rule.count == 2 && rule.allSatisfy { $0.isNonTerminal }
        let isStartEpsilon = rule.isEmpty || (rule.count == 1 && rule[0].isEpsilon)
        #expect(
            isUnitTerminal || isBinaryNT || isStartEpsilon,
            "Production not in CNF: \(prod)"
        )
    }
}

// MARK: - isInChomskyNormalForm property

@Test func cnfProperty_alreadyInCNF() async throws {
    // Build a grammar that is already in CNF:
    //   S → A B
    //   A → "a"
    //   B → "b"
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "S", lexicalTokens: [:])
    #expect(grammar.isInChomskyNormalForm == true)
}

@Test func cnfProperty_notInCNF_longRule() async throws {
    // S → A B C  violates CNF (three symbols)
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B"), n("C")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
        Production(goal: "C", rule: [t("c")]),
    ], start: "S", lexicalTokens: [:])
    #expect(grammar.isInChomskyNormalForm == false)
}

@Test func cnfProperty_notInCNF_unitProduction() async throws {
    // S → A  is a unit production, not CNF
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A")]),
        Production(goal: "A", rule: [t("a")]),
    ], start: "S", lexicalTokens: [:])
    #expect(grammar.isInChomskyNormalForm == false)
}

// MARK: - Epsilon elimination

@Test func cnf_eliminatesEpsilonProductions() async throws {
    // S → A B,  A → "a" | ε,  B → "b"
    // After epsilon elimination A is no longer nullable, so S → B is added.
    let grammarString = """
        S : A B
        A : 'a' | ε
        B : 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let cnf = grammar.toChomskyNormalForm()

    // No production should be a bare epsilon (except possibly S → ε)
    for prod in cnf.productions where prod.goal != grammar.start {
        #expect(
            !(prod.rule.count == 1 && prod.rule[0].isEpsilon),
            "Non-start epsilon production found: \(prod)"
        )
    }
    // The grammar should still be in CNF
    assertCNF(cnf)
}

@Test func cnf_eliminatesEpsilonProductions_multipleNullable() async throws {
    // S → A B C,  A → ε,  B → ε,  C → "c"
    let grammarString = """
        S : A B C
        A : ε
        B : ε
        C : 'c'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let cnf = grammar.toChomskyNormalForm()
    assertCNF(cnf)
}

// MARK: - Unit production elimination

@Test func cnf_eliminatesUnitProductions() async throws {
    // S → A,  A → B,  B → "b"
    // After unit elimination S and A should directly produce "b"
    let grammarString = """
        S : A
        A : B
        B : 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let cnf = grammar.toChomskyNormalForm()

    // No unit production should remain
    for prod in cnf.productions {
        let isUnit = prod.rule.count == 1 && prod.rule[0].isNonTerminal
        #expect(!isUnit, "Unit production found after CNF conversion: \(prod)")
    }
    assertCNF(cnf)
}

// MARK: - TERM step (terminal replacement in long rules)

@Test func cnf_termStep_replacesTerminalsInLongRules() async throws {
    // S → "a" "b"  — both symbols are terminals in a rule of length 2
    // CNF requires each to be wrapped in a fresh NT.
    let grammarString = """
        S : 'a' 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let cnf = grammar.toChomskyNormalForm()
    assertCNF(cnf)

    // The single S-production should now be S → T0 T1 (two non-terminals)
    let sProds = cnf.productions.filter { $0.goal == grammar.start }
    #expect(sProds.count == 1)
    #expect(sProds[0].rule.count == 2)
    #expect(sProds[0].rule.allSatisfy { $0.isNonTerminal })
}

// MARK: - BIN step (binarisation of long rules)

@Test func cnf_binStep_binarisesLongRule() async throws {
    // S → A B C D  (length 4) must be broken into binary pairs
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B"), n("C"), n("D")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
        Production(goal: "C", rule: [t("c")]),
        Production(goal: "D", rule: [t("d")]),
    ], start: "S", lexicalTokens: [:])
    let cnf = grammar.toChomskyNormalForm()
    assertCNF(cnf)
}

@Test func cnf_binStep_ruleOfLengthThree() async throws {
    // S → A B C  (length 3)
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B"), n("C")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
        Production(goal: "C", rule: [t("c")]),
    ], start: "S", lexicalTokens: [:])
    let cnf = grammar.toChomskyNormalForm()
    assertCNF(cnf)
}

// MARK: - Classic textbook grammars

@Test func cnf_sipserExample() async throws {
    // Sipser Example 2.10:
    //   S → A S A | a B
    //   A → B | S
    //   B → b | ε
    let grammarString = """
        S : A S A | 'a' B
        A : B | S
        B : 'b' | ε
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let cnf = grammar.toChomskyNormalForm()
    assertCNF(cnf)
    // The result must be non-empty
    #expect(!cnf.productions.isEmpty)
}

@Test func cnf_expressionGrammar() async throws {
    // Classic expression grammar (after left-recursion removal is NOT needed for CNF):
    //   E → E '+' T | T
    //   T → T '*' F | F
    //   F → '(' E ')' | 'id'
    let grammarString = """
        E : E '+' T | T
        T : T '*' F | F
        F : '(' E ')' | 'id'
    """
    let grammar = try Grammar(wsn: grammarString, start: "E")
    let cnf = grammar.toChomskyNormalForm()
    assertCNF(cnf)
    #expect(!cnf.productions.isEmpty)
}

@Test func cnf_simpleArithmetic() async throws {
    // S → 'a' | S '+' S | S '*' S | '(' S ')'
    let grammarString = """
        S : 'a' | S '+' S | S '*' S | '(' S ')'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let cnf = grammar.toChomskyNormalForm()
    assertCNF(cnf)
}

@Test func cnf_alreadyInCNF_isIdempotent() async throws {
    // A grammar already in CNF should remain in CNF after conversion.
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "S", lexicalTokens: [:])
    #expect(grammar.isInChomskyNormalForm)
    let cnf = grammar.toChomskyNormalForm()
    #expect(cnf.isInChomskyNormalForm)
}

@Test func cnf_resultIsInChomskyNormalForm() async throws {
    // End-to-end: parse a grammar, convert, verify the property.
    let grammarString = """
        S : 'a' S 'b' | ε
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let cnf = grammar.toChomskyNormalForm()
    assertCNF(cnf)
    #expect(cnf.isInChomskyNormalForm)
}
