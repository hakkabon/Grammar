import Testing
@testable import Grammar

// MARK: - Extended FIRST/FOLLOW Set Tests
//
// These tests cover additional edge cases and scenarios for FIRST and FOLLOW set computation.

let eps: Symbol = Symbol.terminal(.meta(MetaTerminal.eps))
let eof: Symbol = Symbol.terminal(.meta(.eof))

// MARK: - FIRST Set Tests

@Test func firstSet_singleTerminal() async throws {
    // Grammar: S → "a"
    let grammarString = """
        S : 'a'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (first, _) = grammar.firstAndFollow()
    
    let calculated = first[n("S")]!
    let expected = Set<Symbol>([t("a")])
    #expect(calculated == expected, "FIRST(S) should be {a}")
}

@Test func firstSet_multipleAlternatives() async throws {
    // Grammar: S → "a" | "b" | "c"
    let grammarString = """
        S : 'a' | 'b' | 'c'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (first, _) = grammar.firstAndFollow()
    
    let calculated = first[n("S")]!
    let expected = Set<Symbol>([t("a"), t("b"), t("c")])
    #expect(calculated == expected, "FIRST(S) should be {a, b, c}")
}

@Test func firstSet_nullableNonTerminal() async throws {
    // Grammar: S → A "b", A → "a" | ε
    let grammarString = """
        S : A 'b'
        A : 'a' | ε
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (first, _) = grammar.firstAndFollow()
    
    let sCalculated = first[n("S")]!
    let sExpected = Set<Symbol>([t("a"), t("b")])
    #expect(sCalculated == sExpected, "FIRST(S) should be {a, b} because A is nullable")
    
    let aCalculated = first[n("A")]!
    let aExpected = Set<Symbol>([t("a"), eps])
    #expect(aCalculated == aExpected, "FIRST(A) should be {a, ε}")
}

@Test func firstSet_chainOfNullables() async throws {
    // Grammar: S → A B C, A → ε, B → ε, C → "c"
    let grammarString = """
        S : A B C
        A : ε
        B : ε
        C : 'c'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (first, _) = grammar.firstAndFollow()
    
    let calculated = first[n("S")]!
    let expected = Set<Symbol>([t("c")])
    #expect(calculated == expected, "FIRST(S) should be {c} - skips nullable A and B")
}

@Test func firstSet_allNullable() async throws {
    // Grammar: S → A B, A → ε, B → ε
    let grammarString = """
        S : A B
        A : ε
        B : ε
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (first, _) = grammar.firstAndFollow()
    
    let calculated = first[n("S")]!
    let expected = Set<Symbol>([eps])
    #expect(calculated == expected, "FIRST(S) should be {ε} when all symbols are nullable")
}

@Test func firstSet_indirectDerivation() async throws {
    // Grammar: S → A, A → B, B → "b"
    let grammarString = """
        S : A
        A : B
        B : 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (first, _) = grammar.firstAndFollow()
    
    let calculated = first[n("S")]!
    let expected = Set<Symbol>([t("b")])
    #expect(calculated == expected, "FIRST(S) should be {b} through indirect derivation")
}

@Test func firstSet_leftRecursive() async throws {
    // Grammar: E → E "+" T | T, T → "n"
    let grammarString = """
        E : E '+' T | T
        T : 'n'
    """
    let grammar = try Grammar(wsn: grammarString, start: "E")
    let (first, _) = grammar.firstAndFollow()
    
    let calculated = first[n("E")]!
    let expected = Set<Symbol>([t("n")])
    #expect(calculated == expected, "FIRST(E) should be {n} even with left recursion")
}

// MARK: - FOLLOW Set Tests

@Test func followSet_startSymbol() async throws {
    // Grammar: S → "a"
    let grammarString = """
        S : 'a'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (_, follow) = grammar.firstAndFollow()
    
    let calculated = follow[NonTerminal(name: "S")]!
    let expected = Set<Symbol>([eof])
    #expect(calculated == expected, "FOLLOW(S) should always contain $")
}

@Test func followSet_terminalAfter() async throws {
    // Grammar: S → A "b", A → "a"
    let grammarString = """
        S : A 'b'
        A : 'a'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (_, follow) = grammar.firstAndFollow()
    
    let calculated = follow[NonTerminal(name: "A")]!
    let expected = Set<Symbol>([t("b")])
    #expect(calculated == expected, "FOLLOW(A) should be {b}")
}

@Test func followSet_nonTerminalAfter() async throws {
    // Grammar: S → A B, A → "a", B → "b"
    let grammarString = """
        S : A B
        A : 'a'
        B : 'b'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (_, follow) = grammar.firstAndFollow()
    
    let aCalculated = follow[NonTerminal(name: "A")]!
    let aExpected = Set<Symbol>([t("b")])
    #expect(aCalculated == aExpected, "FOLLOW(A) should be {b} from FIRST(B)")
    
    let bCalculated = follow[NonTerminal(name: "B")]!
    let bExpected = Set<Symbol>([eof])
    #expect(bCalculated == bExpected, "FOLLOW(B) should be {$}")
}

@Test func followSet_nullableAfter() async throws {
    // Grammar: S → A B C, A → "a", B → ε, C → "c"
    let grammarString = """
        S : A B C
        A : 'a'
        B : ε
        C : 'c'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (_, follow) = grammar.firstAndFollow()
    
    let aCalculated = follow[NonTerminal(name: "A")]!
    let aExpected = Set<Symbol>([t("c")])
    #expect(aCalculated == aExpected, "FOLLOW(A) should be {c} - skips nullable B")
}

@Test func followSet_atEnd() async throws {
    // Grammar: S → A, A → "a"
    let grammarString = """
        S : A
        A : 'a'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (_, follow) = grammar.firstAndFollow()
    
    let calculated = follow[NonTerminal(name: "A")]!
    let expected = Set<Symbol>([eof])
    #expect(calculated == expected, "FOLLOW(A) should be {$} when at end of production")
}

@Test func followSet_propagation() async throws {
    // Grammar: S → A B, A → C, B → ε, C → "c"
    // FOLLOW(A) should include FOLLOW(S) because B is nullable
    let grammarString = """
        S : A B
        A : C
        B : ε
        C : 'c'
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (_, follow) = grammar.firstAndFollow()
    
    let aCalculated = follow[NonTerminal(name: "A")]!
    #expect(aCalculated.contains(eof), "FOLLOW(A) should contain $ from FOLLOW(S)")
}

@Test func followSet_recursiveGrammar() async throws {
    // Grammar: S → "(" S ")" | ε
    let grammarString = """
        S : '(' S ')' | ε
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (_, follow) = grammar.firstAndFollow()
    
    let calculated = follow[NonTerminal(name: "S")]!
    let expected = Set<Symbol>([eof, t(")")])
    #expect(calculated == expected, "FOLLOW(S) should be {$, )}")
}

// MARK: - Combined FIRST/FOLLOW Tests

@Test func firstFollow_balancedParentheses() async throws {
    // Grammar: S → "(" S ")" S | ε
    let grammarString = """
        S : '(' S ')' S | ε
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (first, follow) = grammar.firstAndFollow()
    
    let firstCalculated = first[n("S")]!
    let firstExpected = Set<Symbol>([t("("), eps])
    #expect(firstCalculated == firstExpected, "FIRST(S) should be {(, ε}")
    
    let followCalculated = follow[NonTerminal(name: "S")]!
    let followExpected = Set<Symbol>([eof, t(")")])
    #expect(followCalculated == followExpected, "FOLLOW(S) should be {$, )}")
}

@Test func firstFollow_arithmeticExpression() async throws {
    // Grammar: E → T E', E' → "+" T E' | ε, T → F T', T' → "*" F T' | ε, F → "(" E ")" | "id"
    let grammarString = """
        E  : T Ex
        Ex : '+' T Ex | ε
        T  : F Tx
        Tx : '*' F Tx | ε
        F  : '(' E ')' | 'id'
    """
    let grammar = try Grammar(wsn: grammarString, start: "E")
    let (first, follow) = grammar.firstAndFollow()
    
    // FIRST sets
    let eFirst = first[n("E")]!
    #expect(eFirst == Set<Symbol>([t("("), t("id")]), "FIRST(E) should be {(, id}")
    
    let exFirst = first[n("Ex")]!
    #expect(exFirst == Set<Symbol>([t("+"), eps]), "FIRST(Ex) should be {+, ε}")
    
    let tFirst = first[n("T")]!
    #expect(tFirst == Set<Symbol>([t("("), t("id")]), "FIRST(T) should be {(, id}")
    
    let txFirst = first[n("Tx")]!
    #expect(txFirst == Set<Symbol>([t("*"), eps]), "FIRST(Tx) should be {*, ε}")
    
    let fFirst = first[n("F")]!
    #expect(fFirst == Set<Symbol>([t("("), t("id")]), "FIRST(F) should be {(, id}")
    
    // FOLLOW sets
    let eFollow = follow[NonTerminal(name: "E")]!
    #expect(eFollow == Set<Symbol>([eof, t(")")]), "FOLLOW(E) should be {$, )}")
    
    let tFollow = follow[NonTerminal(name: "T")]!
    #expect(tFollow == Set<Symbol>([eof, t(")"), t("+")]), "FOLLOW(T) should be {$, ), +}")
    
    let fFollow = follow[NonTerminal(name: "F")]!
    #expect(fFollow == Set<Symbol>([eof, t(")"), t("+"), t("*")]), "FOLLOW(F) should be {$, ), +, *}")
}

// MARK: - Edge Cases

@Test func firstFollow_emptyProduction() async throws {
    // Grammar: S → ε
    let grammarString = """
        S : ε
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (first, follow) = grammar.firstAndFollow()
    
    let firstCalculated = first[n("S")]!
    #expect(firstCalculated == Set<Symbol>([eps]), "FIRST(S) should be {ε}")
    
    let followCalculated = follow[NonTerminal(name: "S")]!
    #expect(followCalculated == Set<Symbol>([eof]), "FOLLOW(S) should be {$}")
}

@Test func firstFollow_multipleOccurrences() async throws {
    // Grammar: S → A A A, A → "a" | ε
    let grammarString = """
        S : A A A
        A : 'a' | ε
    """
    let grammar = try Grammar(wsn: grammarString, start: "S")
    let (first, follow) = grammar.firstAndFollow()
    
    let sFirst = first[n("S")]!
    #expect(sFirst == Set<Symbol>([t("a"), eps]), "FIRST(S) should be {a, ε}")
    
    let aFollow = follow[NonTerminal(name: "A")]!
    #expect(aFollow.contains(t("a")), "FOLLOW(A) should contain 'a' from subsequent A")
    #expect(aFollow.contains(eof), "FOLLOW(A) should contain $ from end position")
}
