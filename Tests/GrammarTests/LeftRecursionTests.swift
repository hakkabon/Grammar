import Testing
@testable import Grammar

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
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.eliminateLeftRecursion()
    print("productions: \n \(productions)")
    print("Eliminated left recursion: \n \(leftFactoredProductions)")
}

// Dragon book, Example 4.20, Grammar (4.18)
@Test func eliminateLeftRecursionDragon() async throws {
    let grammarString = """
        S : A 'a' | 'b'
        A : A 'c' | S 'd' | ϵ
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.eliminateLeftRecursion()
    print("productions: \n \(productions)")
    print("Eliminated left recursion: \n \(leftFactoredProductions)")
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
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.eliminateLeftRecursion()
    print("productions: \n \(productions)")
    print("Eliminated left recursion: \n \(leftFactoredProductions)")
}

@Test func eliminateLeftRecursionSimple() async throws {
    let grammarString = """
        A : B 'a' | 'c'
        B : A 'b' | 'd'
    """
    let grammar = try Grammar(wsn: grammarString, start: "A")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.eliminateLeftRecursion()
    print("productions: \n \(productions)")
    print("Eliminated left recursion: \n \(leftFactoredProductions)")
    // expected result of left recursion elimination:
    // A -> B "a"
    // A -> "c"
    // B -> "c" "a" B
    // B -> "d" B
    // B -> "a" "b" B
    // B -> ε
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
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.eliminateLeftRecursion()
    print("productions: \n \(productions)")
    print("Eliminated left recursion: \n \(leftFactoredProductions)")
    // expected result of left recursion elimination:
    // E → T E'
    // E' → + T E'
    // E' → ε
    // T → F T'
    // T' → * F T'
    // T' → ε
    // F → ( E )
    // F → id
}
