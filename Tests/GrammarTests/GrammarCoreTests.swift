import Testing
@testable import Grammar

// MARK: - Grammar core property tests

@Test func grammar_nonTerminals_computedFromProductions() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B")]),
        Production(goal: "A", rule: [t("a")]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "S", lexicalTokens: [:])
    
    let nts = grammar.nonTerminals
    #expect(nts.contains(NonTerminal(name: "S")))
    #expect(nts.contains(NonTerminal(name: "A")))
    #expect(nts.contains(NonTerminal(name: "B")))
    #expect(nts.count == 3)
}

@Test func grammar_terminals_computedFromProductions() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [t("a"), t("b")]),
    ], start: "S", lexicalTokens: [:])
    
    let ts = grammar.terminals
    #expect(ts.contains(Terminal(string: "a")))
    #expect(ts.contains(Terminal(string: "b")))
    #expect(ts.count == 2)
}

@Test func grammar_startProduction_found() {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A")]),
        Production(goal: "A", rule: [t("a")]),
    ], start: "S", lexicalTokens: [:])
    
    #expect(grammar.startProduction?.goal == NonTerminal(name: "S"))
}

@Test func grammar_startProduction_notFound() {
    let grammar = Grammar(productions: [
        Production(goal: "A", rule: [t("a")]),
    ], start: "S", lexicalTokens: [:])
    
    #expect(grammar.startProduction == nil)
}

@Test func grammar_nullableNonTerminals_directEpsilon() {
    let grammar = Grammar(productions: [
        Production(goal: "A", rule: [Symbol.terminal(.meta(.eps))]),
        Production(goal: "B", rule: [t("b")]),
    ], start: "A", lexicalTokens: [:])
    
    #expect(grammar.nullableNonTerminals.contains(NonTerminal(name: "A")))
    #expect(!grammar.nullableNonTerminals.contains(NonTerminal(name: "B")))
}

@Test func grammar_nullableNonTerminals_indirectEpsilon() {
    // S → A B, A → ε, B → ε  ⟹  S is also nullable
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [n("A"), n("B")]),
        Production(goal: "A", rule: [Symbol.terminal(.meta(.eps))]),
        Production(goal: "B", rule: [Symbol.terminal(.meta(.eps))]),
    ], start: "S", lexicalTokens: [:])
    
    #expect(grammar.nullableNonTerminals.contains(NonTerminal(name: "S")))
    #expect(grammar.nullableNonTerminals.contains(NonTerminal(name: "A")))
    #expect(grammar.nullableNonTerminals.contains(NonTerminal(name: "B")))
}

@Test func grammar_equality_sameProductions() {
    let g1 = Grammar(productions: [
        Production(goal: "S", rule: [t("a")])
    ], start: "S", lexicalTokens: [:])
    let g2 = Grammar(productions: [
        Production(goal: "S", rule: [t("a")])
    ], start: "S", lexicalTokens: [:])
    #expect(g1 == g2)
}

@Test func grammar_equality_differentProductions() {
    let g1 = Grammar(productions: [
        Production(goal: "S", rule: [t("a")])
    ], start: "S", lexicalTokens: [:])
    let g2 = Grammar(productions: [
        Production(goal: "S", rule: [t("b")])
    ], start: "S", lexicalTokens: [:])
    #expect(g1 != g2)
}

// MARK: - Grammar notation output

@Test func grammar_bnf_outputContainsExpectedPatterns() async throws {
    let grammar = try Grammar(wsn: """
        S : 'a' | 'b'
    """, start: "S")
    let (prods, _) = grammar.rewriteToStandardForm()
    let standard = Grammar(productions: prods, start: grammar.start, lexicalTokens: [:])
    
    let bnfOutput = standard.bnf
    #expect(bnfOutput.contains("::="))
    #expect(bnfOutput.contains("<S>"))
}

@Test func grammar_ebnf_outputContainsExpectedPatterns() async throws {
    let grammar = try Grammar(wsn: """
        S : 'a' | 'b'
    """, start: "S")
    let (prods, _) = grammar.rewriteToStandardForm()
    let standard = Grammar(productions: prods, start: grammar.start, lexicalTokens: [:])
    
    let ebnfOutput = standard.ebnf
    #expect(ebnfOutput.contains("::="))
}

@Test func grammar_wsn_outputContainsExpectedPatterns() async throws {
    let grammar = try Grammar(wsn: """
        S : 'a' | 'b'
    """, start: "S")
    let (prods, _) = grammar.rewriteToStandardForm()
    let standard = Grammar(productions: prods, start: grammar.start, lexicalTokens: [:])
    
    let wsnOutput = standard.wsn
    #expect(wsnOutput.contains("="))
    #expect(wsnOutput.contains("S"))
}

@Test func grammar_bnf_rendersEpsilonMetaCharacter_forEmptyProduction() async throws {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [])
    ], start: "S", lexicalTokens: [:])
    
    // The default epsilon meta character is 'ε', never a bare quoted empty string.
    #expect(grammar.bnf.contains("ε"))
    #expect(!grammar.bnf.contains("\"\""))
}

@Test func grammar_ebnf_rendersEpsilonMetaCharacter_forEmptyProduction() async throws {
    let grammar = Grammar(productions: [
        Production(goal: "S", rule: [])
    ], start: "S", lexicalTokens: [:])
    
    #expect(grammar.ebnf.contains("ε"))
    #expect(!grammar.ebnf.contains("\"\""))
}

@Test func grammar_wsn_rendersConfiguredEpsilonMetaCharacter() async throws {
    var grammar = Grammar(productions: [
        Production(goal: "S", rule: [])
    ], start: "S", lexicalTokens: [:])
    
    // A grammar may choose 'λ' instead of the default 'ε' for display.
    grammar.epsilon = .lambda
    #expect(grammar.wsn.contains("λ"))
    #expect(!grammar.wsn.contains("\"\""))
}

// MARK: - Grammar import from text

@Test func grammar_import_bnf_basicProduction() async throws {
    let grammar = try Grammar(bnf: """
        <S> ::= 'a' | 'b'
    """, start: "S")
    
    let (prods, _) = grammar.rewriteToStandardForm()
    #expect(prods.count == 2)
}

@Test func grammar_import_wsn_basicProduction() async throws {
    let grammar = try Grammar(wsn: """
        S : 'a' | 'b'
    """, start: "S")
    
    let (prods, _) = grammar.rewriteToStandardForm()
    #expect(prods.count == 2)
}

@Test func grammar_import_wsn_epsilonProduction() async throws {
    let grammar = try Grammar(wsn: """
        S : 'a' | ε
    """, start: "S")
    
    let nts = grammar.nullableNonTerminals
    #expect(nts.contains(NonTerminal(name: "S")))
    
    // The 'ε' alternative must be stored as the canonical empty rule `[]`,
    // not as a production whose rule still contains an epsilon symbol.
    let epsilonProd = grammar.productions.first { $0.goal == NonTerminal(name: "S") && $0.isNullable }
    #expect(epsilonProd?.rule.isEmpty == true)
}

@Test func grammar_import_wsn_multipleRules() async throws {
    let grammar = try Grammar(wsn: """
        S : A B
        A : 'a'
        B : 'b'
    """, start: "S")
    
    let nts = grammar.nonTerminals
    #expect(nts.contains(NonTerminal(name: "S")))
    #expect(nts.contains(NonTerminal(name: "A")))
    #expect(nts.contains(NonTerminal(name: "B")))
}

@Test func grammar_import_wsn_ebnf_option() async throws {
    // [B] becomes a nullable non-terminal
    let grammar = try Grammar(wsn: """
        S : 'a' ['b']
    """, start: "S")
    let (prods, _) = grammar.rewriteToStandardForm()
    // Should have the synthetic optional NT with ε and 'b' productions
    let hasEpsilon = prods.contains { $0.isNullable }
    #expect(hasEpsilon == true)
    // ...and that nullable production's rule is the canonical empty rule.
    #expect(prods.contains { $0.isNullable && $0.rule.isEmpty })
}

@Test func grammar_import_wsn_ebnf_repetition() async throws {
    // {B} becomes a nullable, right-recursive NT
    let grammar = try Grammar(wsn: """
        S : 'a' {'b'}
    """, start: "S")
    let (prods, _) = grammar.rewriteToStandardForm()
    // The repetition NT should have an epsilon production
    let hasEpsilon = prods.contains { $0.isNullable }
    #expect(hasEpsilon == true)
    #expect(prods.contains { $0.isNullable && $0.rule.isEmpty })
}

@Test func grammar_import_wsn_start_isSet() async throws {
    let grammar = try Grammar(wsn: """
        E : T Ex
        Ex : '+' T Ex | ε
        T : 'n'
    """, start: "E")
    
    #expect(grammar.start == NonTerminal(name: "E"))
}

@Test func grammar_import_ebnf() async throws {
    let grammar = try Grammar(ebnf: """
        S = 'a' | 'b' ;
    """, start: "S")
    
    let (prods, _) = grammar.rewriteToStandardForm()
    #expect(prods.count == 2)
}

// MARK: - Standard form rewriting

@Test func standardForm_rewrite_alternativesSplitCorrectly() async throws {
    let grammarString = """
        S : 'a' | 'b' | 'c' | 'd' | 'e'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (prods, _) = grammar.rewriteToStandardForm()
    // Each alternative becomes its own production
    let sProds = prods.filter { $0.goal == NonTerminal(name: "S") }
    #expect(sProds.count == 5)
}

@Test("genNTs → []).isEmpty → true → true) - // A synthetic NT for ['b'] should have been created")
func standardForm_rewrite_optionGeneratesNullable() async throws {
    let grammarString = """
        S : 'a' ['b'] 'c'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    
    // A synthetic NT for ['b'] should have been created
    #expect(!grammar.generatedNonTerminals.isEmpty)
    // That NT should have an epsilon production
    let syntheticEpsProds = grammar.productions.filter { grammar.generatedNonTerminals.contains($0.goal) && $0.isNullable }
    #expect(!syntheticEpsProds.isEmpty)
}

@Test("Unexpectedly found nil while unwrapping an Optional value")
func standardForm_rewrite_repetitionGeneratesSelfReference() async throws {
    let grammarString = """
        S : {'a'}
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    
    #expect(!grammar.generatedNonTerminals.isEmpty)
    // The repetition NT should reference itself
    let repNT = grammar.generatedNonTerminals.first!
    let selfRef = grammar.productions.filter { $0.goal == repNT && $0.generatedNonTerminals.contains(repNT) }
    #expect(!selfRef.isEmpty)
}

@Test func standardForm_rewrite_digitGrammarProducesTenProductions() async throws {
    let grammarString = """
        > <digit>
        <digit> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
    """
    let grammar = try Grammar(gen: grammarString)
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    #expect(standardGrammar.productions.count == 10)
}
