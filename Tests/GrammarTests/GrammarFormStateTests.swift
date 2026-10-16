import Foundation
import Testing
@testable import Grammar

private let stateMachineSource = """
    S : 'a' S 'b' | 'a' 'b'
    """

@Test func grammarFormStandardMatchesTheExplicitRewrite() throws {
    var grammar = try Grammar(wsn: stateMachineSource, start: "S")
    let (productions, generated) = grammar.rewriteToStandardForm()

    grammar.grammarForm = .standard

    #expect(grammar.grammarForm == .standard)
    #expect(Set(grammar.productions) == Set(productions))
    #expect(grammar.generatedNonTerminals == generated)
}

@Test func grammarFormChomskyMatchesThePureConversionPipeline() throws {
    var grammar = try Grammar(wsn: stateMachineSource, start: "S")
    let (productions, generated) = grammar.rewriteToStandardForm()
    let standard = Grammar(
        productions: productions,
        start: grammar.start,
        empty: grammar.epsilon,
        lexicalTokens: grammar.lexicalTokens,
        generatedNonTerminals: generated
    )
    let expected = standard.toChomskyNormalForm()

    grammar.grammarForm = .chomsky

    #expect(grammar.grammarForm == .chomsky)
    #expect(grammar.isInChomskyNormalForm)
    #expect(Set(grammar.productions) == Set(expected.productions))
    #expect(grammar.generatedNonTerminals == expected.generatedNonTerminals)
}

@Test func grammarFormGreibachMatchesThePureConversionPipeline() throws {
    var grammar = try Grammar(wsn: stateMachineSource, start: "S")
    let (productions, generated) = grammar.rewriteToStandardForm()
    let standard = Grammar(
        productions: productions,
        start: grammar.start,
        empty: grammar.epsilon,
        lexicalTokens: grammar.lexicalTokens,
        generatedNonTerminals: generated
    )
    let expected = standard.toGreibachNormalForm()

    grammar.grammarForm = .greibach

    #expect(grammar.grammarForm == .greibach)
    #expect(grammar.isInGreibachForm)
    #expect(Set(grammar.productions) == Set(expected.productions))
    #expect(grammar.generatedNonTerminals == expected.generatedNonTerminals)
}

@Test func grammarFormNoneIsANoOpAndDoesNotPromiseRestoration() throws {
    var grammar = try Grammar(wsn: stateMachineSource, start: "S")
    grammar.grammarForm = .chomsky
    let transformed = grammar.productions

    grammar.grammarForm = .none

    #expect(grammar.grammarForm == .none)
    #expect(grammar.productions == transformed)
}

@Test func grammarFormCanMoveBetweenConcreteNormalForms() throws {
    var grammar = try Grammar(wsn: stateMachineSource, start: "S")

    grammar.grammarForm = .standard
    grammar.grammarForm = .chomsky
    #expect(grammar.isInChomskyNormalForm)

    grammar.grammarForm = .greibach
    #expect(grammar.isInGreibachForm)

    grammar.grammarForm = .chomsky
    #expect(grammar.isInChomskyNormalForm)
}

@Test func grammarFormRecomputesNullableNonTerminalsAfterReplacingProductions() throws {
    var grammar = try Grammar(wsn: "S : A 'b'\nA : ε | 'a'", start: "S")
    let before = grammar.nullableNonTerminals
    #expect(before.contains(NonTerminal(name: "A")))

    grammar.grammarForm = .chomsky

    #expect(grammar.nullableNonTerminals == grammar.allNullableNonTerminals())
    #expect(grammar.nullableNonTerminals != before)
}

@Test func grammarFormCodableRoundTripPreservesTheSelectedFormAndProductions() throws {
    var grammar = try Grammar(wsn: stateMachineSource, start: "S")
    grammar.grammarForm = .chomsky

    let decoded = try JSONDecoder().decode(Grammar.self, from: JSONEncoder().encode(grammar))

    #expect(decoded.grammarForm == .chomsky)
    #expect(decoded == grammar)
    #expect(decoded.generatedNonTerminals == grammar.generatedNonTerminals)
}
