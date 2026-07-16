import Testing
@testable import Grammar

@Test func testBnfGrammar() async throws {
    let grammar = Grammar.bnfGrammar

    #expect(grammar.start == NonTerminal(name: "syntax"))
    #expect(grammar.productions.isEmpty == false)
    #expect(grammar.nonTerminals.contains(NonTerminal(name: "rule-name")))

    // `symbol` is a flat 31-way top-level alternation of single-character
    // literals - it should become 31 productions for the same goal, with no
    // synthetic non-terminal standing in for the choice.
    let symbolProductions = grammar.productions.filter { $0.goal == NonTerminal(name: "symbol") }
    #expect(symbolProductions.count == 31)
    #expect(symbolProductions.allSatisfy { $0.rule.count == 1 && $0.rule.first?.isTerminal == true })

    print("symbol productions: \n \(symbolProductions) \n")
    
    // `letter` is defined via an inline regex terminal (`rt(...)`), not a
    // reference to another rule.
    let letterProduction = grammar.productions.first { $0.goal == NonTerminal(name: "letter") }
    #expect(letterProduction?.rule.first?.isTerminal == true)
}

@Test func testEbnfGrammar() async throws {
    let grammar = Grammar.ebnfGrammar

    #expect(grammar.start == NonTerminal(name: "syntax"))
    #expect(grammar.productions.isEmpty == false)
    #expect(grammar.nonTerminals.contains(NonTerminal(name: "factor")))

    // `termination` is a plain two-way alternation: `.` | `;`.
    let terminationProductions = grammar.productions.filter { $0.goal == NonTerminal(name: "termination") }
    #expect(terminationProductions.count == 2)
}

@Test func testWsnGrammar() async throws {
    let grammar = Grammar.wsnGrammar

    #expect(grammar.start == NonTerminal(name: "syntax"))
    #expect(grammar.productions.isEmpty == false)
    #expect(grammar.nonTerminals.contains(NonTerminal(name: "factor")))

    // `terminator` is a plain two-way alternation: ";" | ".".
    let terminatorProductions = grammar.productions.filter { $0.goal == NonTerminal(name: "terminator") }
    #expect(terminatorProductions.count == 2)

    // `factor` mixes plain references with Opt/Grp/Seq - each of those
    // branches should resolve to a synthetic non-terminal standing in for
    // the parenthesized/bracketed/braced sub-expression.
    let factorProductions = grammar.productions.filter { $0.goal == NonTerminal(name: "factor") }
    #expect(factorProductions.count == 5)
}
