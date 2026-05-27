import Testing
@testable import Grammar

let eps: Symbol = Symbol.terminal(.meta(MetaTerminal.eps))
let eof: Symbol = Symbol.terminal(.meta(.eof))

@Test func firstFollowTest_1() async throws {
    let grammarString = """
        <A> ::= 'a' <B> ;
        <A> ::= 'b' ;
        <A> ::= ε ;   
    """
    let grammar = try Grammar(bnf: grammarString, start: "A")
    let (first,_) = grammar.firstAndFollow()
    let calculatedSet: Set<Symbol> = first[n("A")]!
    let expectedSet = Set<Symbol>([t("a"), t("b"), eps])
    #expect(calculatedSet == expectedSet)
}

@Test func firstFollowTest_2() async throws {
    let grammarString = """
        <X> : <A> <B> <C> ;
        <A> : 'a' | ε ;
        <B> : 'b' | ε ;   
        <C> : 'c' | 'd' ;
    """
    let grammar = try Grammar(bnf: grammarString, start: "X")
    let (first,follow) = grammar.firstAndFollow()

    let x_calculated = first[n("X")]!
    #expect(x_calculated == Set<Symbol>([t("a"), t("b"), t("c"), t("d")]))
    let a_calculated = first[n("A")]!
    #expect(a_calculated == Set<Symbol>([t("a"), eps]))
    let b_calculated = first[n("B")]!
    #expect(b_calculated == Set<Symbol>([t("b"), eps]))
    let c_calculated = first[n("C")]!
    #expect(c_calculated == Set<Symbol>([t("c"), t("d")]))
    
    let x_follow_calculated = follow[NonTerminal(name: "X")]!
    #expect(x_follow_calculated == Set<Symbol>([eof]))
    let a_follow_calculated = follow[NonTerminal(name: "A")]!
    #expect(a_follow_calculated == Set<Symbol>([t("b"), t("c"), t("d")]))
    let b_follow_calculated = follow[NonTerminal(name: "B")]!
    #expect(b_follow_calculated == Set<Symbol>([t("c"), t("d")]))
    let c_follow_calculated = follow[NonTerminal(name: "C")]!
    #expect(c_follow_calculated == Set<Symbol>([eof]))
}

@Test func firstFollowTest_3() async throws {
    let grammarString = """
        X : T 'n' S ;
        X : R 'm' ;
        T : 'q' ;
        T : ε ;
        S : 'p' ;
        S : ε ;
        R : 'o' 'm' ;
        R : S T ;
    """
    let grammar = try Grammar(wsn: grammarString, start: "X")
    let (first,follow) = grammar.firstAndFollow()

    let calculatedFirstSet = first[n("X")]!
    let expectedFirstSet = Set<Symbol>([t("q"), t("n"), t("o"), t("p"), t("m")])
    #expect(calculatedFirstSet == expectedFirstSet)

    let calculatedFollowSet = follow[NonTerminal(name: "S")]!
    let expectedFollowSet = Set<Symbol>([eof, t("q"), t("m")])
    #expect(calculatedFollowSet == expectedFollowSet)
}

@Test func firstFollowTest_4() async throws {
    let grammarString = """
        E : E '+' T | T ;
        T : T '*' F | F ;
        F : '(' E ')' | ID | ε ;
        ID : '1' | '2' | '3' | '4' | '5' ;    
    """
    let grammar = try Grammar(wsn: grammarString, start: "E")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let (first,follow) = standardGrammar.firstAndFollow()

    let calculatedFirstSet = first[n("E")]!
    let expectedFirstSet = Set<Symbol>([t("("), t("*"), t("+"), t("1"), t("2"), t("3"), t("4"), t("5"), eps])
    #expect(calculatedFirstSet == expectedFirstSet)

    let calculatedFollowSet = follow[NonTerminal(name: "T")]!
    let expectedFollowSet = Set<Symbol>([eof, t(")"), t("*"), t("+")])
    #expect(calculatedFollowSet == expectedFollowSet)
}

@Test func firstFollowTest_5() async throws {
    let grammarString = """
        E  : T Ex
        Ex : '+' T Ex | ε
        T  : F Tx
        Tx : '*' F Tx | ε
        F  : '(' E ')' | ID
        ID : '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'    
    """
    let grammar = try Grammar(wsn: grammarString, start: "E")
    let (productions, _) = grammar.rewriteToStandardForm()
    let standardGrammar = Grammar(productions: productions, start: grammar.start, lexicalTokens: [:])
    let (first,follow) = standardGrammar.firstAndFollow()

    let calculatedFirstSet = first[n("E")]!
    let expectedFirstSet = Set<Symbol>([t("("),t("1"),t("2"),t("3"),t("4"),t("5"),t("6"),t("7"),t("8"),t("9")])
    #expect(calculatedFirstSet == expectedFirstSet)

    let calculatedFollowSet = follow[NonTerminal(name: "T")]!
    let expectedFollowSet = Set<Symbol>([eof,t(")"),t("+")])
    #expect(calculatedFollowSet == expectedFollowSet)
}
