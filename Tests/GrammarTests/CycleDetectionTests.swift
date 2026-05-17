import Testing
@testable import Grammar

// Very simple cyclic Grammar
@Test func cycleDetectionGrammar_1() async throws {
    
    let grammarString = """
        S : A
        A : B
        B : C
        C : A
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let cycles = standardGrammar.detectCycles()
    #expect(cycles.isEmpty == false)
    if !cycles.isEmpty {
        print("cycles detected: \(cycles)")
    }
}

// A non-cyclic Grammar
@Test func cycleDetectionGrammar_2() async throws {
    
    let grammarString = """
        S : AB
        A : 'a'
        B : 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let cycles = standardGrammar.detectCycles()
    #expect(cycles.isEmpty == true)
}
