import Testing
@testable import Grammar

@Test func testAlternativeRewrite() async throws {
    let grammarString = """
    > <digit>
    <digit> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
    """
    let grammar = try Grammar(gen: grammarString)
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])

    #expect(standardGrammar.productions.count == 10)
}
