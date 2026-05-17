import Testing
@testable import Grammar

// Crafting a Compiler, 5.5. Obtaining LL(1) Grammars
@Test func leftFactoringIfElse() async throws {
    
    let grammarString = """
        Stmt     : 'if' Expr 'then' StmtList 'endif'
                 | 'if' Expr 'then' StmtList 'else' StmtList 'endif'
        StmtList : StmtList ';' Stmt
                 | Stmt      
        Expr     : 'var' + Expr
                 | 'var'
    """
    let grammar = try Grammar(wsn: grammarString, start: "Stmt")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.leftFactoring()
    print("productions: \n \(productions)")
    print("Left factored productions: \n \(leftFactoredProductions)")
}

@Test func leftFactoringExample_1() async throws {
    
    let grammarString = """
        S : 'b' S S 'a' 'a' S | 'b' S S 'a' S 'b' | 'b' S 'b' | 'a'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.leftFactoring()
    print("productions: \n \(productions)")
    print("Left factored productions: \n \(leftFactoredProductions)")
    // S → bSS’ | a
    // S’ → SaA | b
    // A → aS | Sb
}

@Test func leftFactoringExample_2() async throws {
    
    let grammarString = """
        S : 'a' | 'a' 'b' | 'a' 'b' 'c' | 'a' 'b' 'c' 'd'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.leftFactoring()
    print("productions: \n \(productions)")
    print("Left factored productions: \n \(leftFactoredProductions)")
}
