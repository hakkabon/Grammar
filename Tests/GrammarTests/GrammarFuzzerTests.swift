import Testing
@testable import Grammar

/// `Terminal.description` renders plain string terminals with surrounding
/// quotes (e.g. `"a"`), which is right for pretty-printing a grammar but not
/// for reconstructing the literal string a derivation generates. These tests
/// only use plain string terminals, so unwrap the raw value directly.
private func rawValue(_ terminal: Terminal) -> String {
    guard case .string(let string) = terminal else {
        return terminal.description
    }
    return string
}

// These tests guard against a regression where `GrammarFuzzer` would hang
// indefinitely on grammars containing an epsilon (nullable) production.
//
// Root cause: `DerivationTree.node` used to store its children as a plain,
// non-optional `MutableList`, with an *empty* list overloaded to mean two
// different things: "not yet expanded" (a freshly created placeholder) and
// "expanded via `A ::= ε`, and therefore permanently done". Since both
// states looked identical (`children.count == 0`), `anyPossibleExpansions`
// treated an epsilon-resolved node as still needing expansion forever, so
// the fuzzer's final, unbounded closing phase (`expandNodeMinCost`) never
// terminated for any grammar reachable through a nullable non-terminal.
//
// The fix makes `derivations` an `Optional<MutableList<...>>`: `nil` means
// "not yet expanded", `.some([])` means "expanded to nothing". If this
// regression ever comes back, the tests below will hang rather than fail
// outright — that hang (timeout) is itself the signal.

@Test func fuzzer_terminatesForGrammarWithDirectEpsilonProduction() throws {
    // Exactly the grammar reported as stalling:
    //   S ::= S T
    //   S ::= 'a'
    //   B ::= ε
    //   T ::= 'a' B
    //   T ::= 'a'
    let bnf = """
    <S> ::= <S> <T>
    <S> ::= 'a'
    <B> ::= ε
    <T> ::= 'a' <B>
    <T> ::= 'a'
    """
    let grammar = try Grammar(bnf: bnf, start: "S")
    let fuzzer = GrammarFuzzer(grammar: grammar, options: .init(trace: false))

    // Repeat many times: expansion choices are randomized, and the bug only
    // manifests on paths that pick the `T ::= 'a' <B>` branch, so a single
    // run could get lucky and never hit the nullable non-terminal at all.
    for _ in 0..<200 {
        let tree = fuzzer.fuzz(start: "S")

        // Every generated string in this grammar's language is one or more 'a's.
        let generated = tree.leafs.map(rawValue).joined()
        #expect(!generated.isEmpty)
        #expect(generated.allSatisfy { $0 == "a" })
    }
}

@Test func fuzzer_terminatesWhenEpsilonNonTerminalAppearsMultipleTimes() throws {
    // A non-terminal that derives ε and is referenced by more than one
    // sibling in the same production, to make sure the fix isn't
    // accidentally only correct for a single occurrence.
    let bnf = """
    <S> ::= <A> 'x' <A> 'y' <A>
    <A> ::= ε
    """
    let grammar = try Grammar(bnf: bnf, start: "S")
    let fuzzer = GrammarFuzzer(grammar: grammar, options: .init(trace: false))

    for _ in 0..<50 {
        let tree = fuzzer.fuzz(start: "S")
        let generated = tree.leafs.map(rawValue).joined()
        #expect(generated == "xy")
    }
}

@Test func fuzzer_terminatesForTransitivelyNullableNonTerminal() throws {
    // B is nullable only transitively, through C.
    let bnf = """
    <S> ::= <S> 'a' <B>
    <S> ::= 'a'
    <B> ::= <C>
    <C> ::= ε
    """
    let grammar = try Grammar(bnf: bnf, start: "S")
    let fuzzer = GrammarFuzzer(grammar: grammar, options: .init(trace: false))

    for _ in 0..<100 {
        let tree = fuzzer.fuzz(start: "S")
        #expect(tree.leafs.allSatisfy { rawValue($0) == "a" })
    }
}
