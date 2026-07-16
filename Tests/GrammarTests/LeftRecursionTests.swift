import Testing
@testable import Grammar

// Helper to verify that no direct left-recursion exists in the resulting productions
private func assertNoLeftRecursion(_ productions: [Production]) {
    for prod in productions {
        #expect(prod.rule.first != .nonTerminal(prod.goal), "Direct left-recursion found: \(prod)")
    }
}

// Crafting a Compiler, 5.5. Obtaining LL(1) Grammars
@Test func eliminateLeftRecursionIfElse() async throws {
    let grammarString = """
        Stmt     : 'if' Expr 'then' StmtList V1
        V1       : 'endif'
                 | 'else' StmtList 'endif'
        StmtList : StmtList ';' Stmt
                 | Stmt      
        Expr     : 'var' V2
        V2       : 'var'
                 | ϵ
    """
    let grammar = try Grammar(wsn: grammarString, start: "Stmt")
    let leftFactoredProductions = grammar.eliminateLeftRecursion()
    
    assertNoLeftRecursion(leftFactoredProductions)
    
    let goals = Set(leftFactoredProductions.map { $0.goal })
    #expect(goals.contains("Stmt"))
    #expect(goals.contains("StmtList"))
    #expect(goals.contains(where: { $0.name.hasPrefix("StmtList-") }), "Should generate new non-terminal for StmtList")
}

// Dragon book, Example 4.20, Grammar (4.18)
@Test func eliminateLeftRecursionDragon() async throws {
    let grammarString = """
        S : A 'a' | 'b'
        A : A 'c' | S 'd' | ϵ
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let leftFactoredProductions = grammar.eliminateLeftRecursion()
    
    assertNoLeftRecursion(leftFactoredProductions)
}

// Grune, 6.3.2 A Counterexample: Left Recursion
@Test func eliminateLeftRecursionGrune() async throws {
    let grammarString = """
        S : A B 'c'
        B : C 'd'
        B : A B 'f'
        C : S 'e'
        A : ε
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let leftFactoredProductions = grammar.eliminateLeftRecursion()
    
    assertNoLeftRecursion(leftFactoredProductions)
}

@Test func eliminateLeftRecursionSimple() async throws {
    let grammarString = """
        A : B 'a' | 'c'
        B : A 'b' | 'd'
    """
    let grammar = try Grammar(wsn: grammarString, start: "A")
    let leftFactoredProductions = grammar.eliminateLeftRecursion()
    
    assertNoLeftRecursion(leftFactoredProductions)
    
    let goals = Set(leftFactoredProductions.map { $0.goal })
    #expect(goals.contains("A"))
    #expect(goals.contains("B"))
    #expect(goals.contains(where: { $0.name.hasPrefix("B-") }), "Should generate a new non-terminal for B")
}

// Elaine Rich example p.241
@Test func eliminateLeftRecursionExpression() async throws {
    let grammarString = """
        E : E '+' T
        E : T
        T : T '*' F
        T : F
        F : '(' E ')'
        F : 'id'
    """
    let grammar = try Grammar(wsn: grammarString, start: "E")
    let leftFactoredProductions = grammar.eliminateLeftRecursion()
    print(leftFactoredProductions)
    assertNoLeftRecursion(leftFactoredProductions)
    let goals = Set(leftFactoredProductions.map { $0.goal })
    #expect(goals.contains(where: { $0.name.hasPrefix("E-") }), "Should generate a new non-terminal for E")
    #expect(goals.contains(where: { $0.name.hasPrefix("T-") }), "Should generate a new non-terminal for T")
}
