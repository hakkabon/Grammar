import Testing
@testable import Grammar

// Helper to verify that no two rules for the same non-terminal share a common prefix
private func assertNoCommonPrefixes(_ productions: [Production]) {
    let grouped = Dictionary(grouping: productions, by: \.goal)
    for (goal, prods) in grouped {
        let rules = prods.map { $0.rule }
        // Group rules by their first symbol.
        let nontermGroup = Dictionary(grouping: rules.filter { !$0.isEmpty }) { $0[0] }
        for (firstSym, groupRules) in nontermGroup {
            #expect(groupRules.count == 1, "Goal '\(goal)' has multiple rules starting with '\(firstSym)': \(groupRules)")
        }
    }
}

// Crafting a Compiler, 5.5. Obtaining LL(1) Grammars
@Test func leftFactoringIfElse() async throws {
    let grammarString = """
        Stmt     : 'if' Expr 'then' StmtList 'endif'
                 | 'if' Expr 'then' StmtList 'else' StmtList 'endif'
        StmtList : StmtList ';' Stmt
                 | Stmt      
        Expr     : 'var' Expr
                 | 'var'
    """
    let grammar = try Grammar(wsn: grammarString, start: "Stmt")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.leftFactoring()
    
    assertNoCommonPrefixes(leftFactoredProductions)
    
    let goals = Set(leftFactoredProductions.map { $0.goal })
    #expect(goals.contains("Stmt"))
    #expect(goals.contains(where: { $0.name.hasPrefix("V-") }), "Should generate a new non-terminal for factoring")
}

@Test func leftFactoringExample_1() async throws {
    let grammarString = """
        S : 'b' S S 'a' 'a' S | 'b' S S 'a' S 'b' | 'b' S 'b' | 'a'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.leftFactoring()
    
    assertNoCommonPrefixes(leftFactoredProductions)
    
    let goals = Set(leftFactoredProductions.map { $0.goal })
    #expect(goals.contains("S"))
    #expect(goals.count >= 3, "Should have factored multiple levels")
}

@Test func leftFactoringExample_2() async throws {
    let grammarString = """
        S : 'a' | 'a' 'b' | 'a' 'b' 'c' | 'a' 'b' 'c' 'd'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let leftFactoredProductions = standardGrammar.leftFactoring()
    
    assertNoCommonPrefixes(leftFactoredProductions)
}
