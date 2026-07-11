import Testing
@testable import Grammar

// MARK: - Greibach Normal Form Tests
//
// Reference grammars are taken from standard textbooks:
//   • Hopcroft, Motwani & Ullman, "Introduction to Automata Theory"
//   • Sipser, "Introduction to the Theory of Computation"

// MARK: - Helper

/// Verify that every production in `grammar` satisfies the GNF invariant:
///   • A → a α   where `a` is a terminal and α is a (possibly empty) sequence of non-terminals.
private func assertGNF(_ grammar: Grammar, file: String = #file, line: Int = #line) {
    for prod in grammar.productions {
        let rule = prod.rule
        guard !rule.isEmpty else {
            // Empty rules are not allowed in strict GNF
            #expect(Bool(false), "Empty production found in GNF: \(prod)")
            continue
        }
        // First symbol must be a terminal
        #expect(rule[0].isTerminal, "GNF violation – first symbol is not a terminal: \(prod)")
        // All remaining symbols must be non-terminals
        for sym in rule.dropFirst() {
            #expect(sym.isNonTerminal, "GNF violation – non-terminal position contains non-NT: \(prod)")
        }
    }
}

// MARK: - isInGreibachForm property

@Test func gnfProperty_alreadyInGNF() async throws {
    // Build a grammar that is already in GNF:
    //   S → "a" A B
    //   A → "b"
    //   B → "c" A
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [t("a"), n("A"), n("B")]),
        Production(goal: "A", rule: [t("b")]),
        Production(goal: "B", rule: [t("c"), n("A")]),
    ], start: "S", lexicalTokens: [:])
    #expect(grammar.isInGreibachForm == true)
}

@Test func gnfProperty_notInGNF_startsWithNT() async throws {
    // S → A "b"  violates GNF (starts with non-terminal)
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), t("b")]),
        Production(goal: "A", rule: [t("a")]),
    ], start: "S", lexicalTokens: [:])
    #expect(grammar.isInGreibachForm == false)
}

@Test func gnfProperty_notInGNF_terminalInTail() async throws {
    // S → "a" "b"  violates GNF (second symbol is a terminal, not a non-terminal)
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [t("a"), t("b")]),
    ], start: "S", lexicalTokens: [:])
    #expect(grammar.isInGreibachForm == false)
}

// MARK: - Epsilon elimination (shared with CNF)

@Test func gnf_eliminatesEpsilonProductions() async throws {
    // S → A B,  A → "a" | ε,  B → "b"
    let grammarString = """
        S : A B
        A : 'a' | ε
        B : 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let gnf = grammar.toGreibachNormalForm()

    // No non-start epsilon production should remain
    for prod in gnf.productions where prod.goal != grammar.start {
        #expect(
            !(prod.rule.count == 1 && prod.rule[0].isEpsilon),
            "Non-start epsilon production found: \(prod)"
        )
    }
}

// MARK: - Unit production elimination (shared with CNF)

@Test func gnf_eliminatesUnitProductions() async throws {
    // S → A,  A → B,  B → "b"
    let grammarString = """
        S : A
        A : B
        B : 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let gnf = grammar.toGreibachNormalForm()

    for prod in gnf.productions {
        let isUnit = prod.rule.count == 1 && prod.rule[0].isNonTerminal
        #expect(!isUnit, "Unit production found after GNF conversion: \(prod)")
    }
}

// MARK: - Left recursion elimination

@Test func gnf_eliminatesDirectLeftRecursion() async throws {
    // A → A "a" | "b"   (direct left recursion)
    let grammarString = """
        A : A 'a' | 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "A")
    let gnf = grammar.toGreibachNormalForm()

    // No production should start with a non-terminal
    for prod in gnf.productions {
        if !prod.rule.isEmpty {
            #expect(prod.rule[0].isTerminal, "Left recursion not eliminated: \(prod)")
        }
    }
}

@Test func gnf_eliminatesIndirectLeftRecursion() async throws {
    // S → A "a" | "b"
    // A → S "c" | "d"
    // S indirectly left-recurses through A.
    let grammarString = """
        S : A 'a' | 'b'
        A : S 'c' | 'd'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let gnf = grammar.toGreibachNormalForm()

    for prod in gnf.productions {
        if !prod.rule.isEmpty {
            #expect(prod.rule[0].isTerminal, "Left recursion not eliminated: \(prod)")
        }
    }
}

// MARK: - Classic textbook grammars

@Test func gnf_simpleGrammar_terminalFirst() async throws {
    // S → "a" S "b" | "c"
    // Already starts with terminals — GNF conversion should preserve this.
    let grammarString = """
        S : 'a' S 'b' | 'c'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let gnf = grammar.toGreibachNormalForm()
    assertGNF(gnf)
    #expect(!gnf.productions.isEmpty)
}

@Test func gnf_expressionGrammar() async throws {
    // E → E '+' T | T
    // T → T '*' F | F
    // F → '(' E ')' | 'id'
    let grammarString = """
        E : E '+' T | T
        T : T '*' F | F
        F : '(' E ')' | 'id'
    """
    let grammar = try Grammar(wsn: grammarString, start: "E")
    let gnf = grammar.toGreibachNormalForm()
    assertGNF(gnf)
    #expect(!gnf.productions.isEmpty)
}

@Test func gnf_resultIsInGreibachNormalForm() async throws {
    // End-to-end: parse, convert, verify the property.
    let grammarString = """
        S : 'a' S 'b' | 'a' 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let gnf = grammar.toGreibachNormalForm()
    assertGNF(gnf)
    #expect(gnf.isInGreibachForm)
}

@Test func gnf_alreadyInGNF_isIdempotent() async throws {
    // A grammar already in GNF should remain in GNF after conversion.
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [t("a"), n("A"), n("B")]),
        Production(goal: "A", rule: [t("b")]),
        Production(goal: "B", rule: [t("c"), n("A")]),
    ], start: "S", lexicalTokens: [:])
    #expect(grammar.isInGreibachForm)
    let gnf = grammar.toGreibachNormalForm()
    #expect(gnf.isInGreibachForm)
}

@Test func gnf_nonEmptyResult() async throws {
    // Any non-trivial grammar should produce a non-empty GNF result.
    let grammarString = """
        S : 'a' | 'b' S
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let gnf = grammar.toGreibachNormalForm()
    #expect(!gnf.productions.isEmpty)
    assertGNF(gnf)
}
