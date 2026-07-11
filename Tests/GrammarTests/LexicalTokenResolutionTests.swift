import Testing
@testable import Grammar

// MARK: - StandardNotation: lexical definitions are collected into `lexicalTokens`

@Test func rewriteToStandardNotation_collectsRegexDefinition() throws {
    let syntax = BnfExpression.syntax([
        .regex("Identifier", "[a-zA-Z_][a-zA-Z0-9_]*"),
        .production("primary", .nonterminal("Identifier")),
    ])

    let (_, _, _, _, tokens) = StandardNotation().rewriteToStandardNotation(syntax: syntax)

    #expect(tokens["Identifier"] == (try Terminal(expression: "[a-zA-Z_][a-zA-Z0-9_]*")))
}

@Test func rewriteToStandardNotation_collectsRangeDefinition() {
    let syntax = BnfExpression.syntax([
        .range("Digit", "0", "9"),
        .production("num", .nonterminal("Digit")),
    ])

    let (_, _, _, _, tokens) = StandardNotation().rewriteToStandardNotation(syntax: syntax)

    #expect(tokens["Digit"] == Terminal(range: "0" ... "9"))
}

@Test func rewriteToStandardNotation_collectsListDefinition() {
    let syntax = BnfExpression.syntax([
        .list("Bool", ["true", "false"]),
        .production("literal", .nonterminal("Bool")),
    ])

    let (_, _, _, _, tokens) = StandardNotation().rewriteToStandardNotation(syntax: syntax)

    #expect(tokens["Bool"] == Terminal(list: ["true", "false"]))
}

@Test func rewriteToStandardNotation_ignoresMalformedRange() {
    // Lower bound above upper bound: skipped with a warning rather than trapping
    // when the ClosedRange is constructed.
    let syntax = BnfExpression.syntax([
        .range("Bad", "9", "0"),
        .production("num", .nonterminal("Bad")),
    ])

    let (_, _, _, _, tokens) = StandardNotation().rewriteToStandardNotation(syntax: syntax)

    #expect(tokens["Bad"] == nil)
}

// MARK: - Referenced lexical identifiers become .terminal symbols automatically

@Test func nonterminalReference_toRegexDefinition_becomesTerminal() throws {
    let syntax = BnfExpression.syntax([
        .regex("Identifier", "[a-zA-Z]+"),
        .production("primary", .nonterminal("Identifier")),
    ])

    let (productions, _, _, _, tokens) = StandardNotation().rewriteToStandardNotation(syntax: syntax)

    #expect(productions.count == 1)
    let rule = try #require(productions.first?.rule)
    #expect(rule == [.terminal(try #require(tokens["Identifier"]))])
}

@Test func nonterminalReference_toRangeDefinition_becomesTerminal() {
    let syntax = BnfExpression.syntax([
        .range("Digit", "0", "9"),
        .production("num", .nonterminal("Digit")),
    ])

    let (productions, _, _, _, _) = StandardNotation().rewriteToStandardNotation(syntax: syntax)

    #expect(productions.first?.rule == [.terminal(Terminal(range: "0" ... "9"))])
}

@Test func nonterminalReference_toListDefinition_becomesTerminal() {
    let syntax = BnfExpression.syntax([
        .list("Bool", ["true", "false"]),
        .production("literal", .nonterminal("Bool")),
    ])

    let (productions, _, _, _, _) = StandardNotation().rewriteToStandardNotation(syntax: syntax)

    #expect(productions.first?.rule == [.terminal(Terminal(list: ["true", "false"]))])
}

@Test func nonterminalReference_withoutMatchingLexicalDefinition_staysNonTerminal() {
    let syntax = BnfExpression.syntax([
        .production("A", .nonterminal("B")),
        .production("B", .terminal("x")),
    ])

    let (productions, _, _, _, tokens) = StandardNotation().rewriteToStandardNotation(syntax: syntax)

    #expect(tokens.isEmpty)
    let ruleForA = productions.first { $0.goal == NonTerminal(name: "A") }?.rule
    #expect(ruleForA == [.nonTerminal(NonTerminal(name: "B"))])
}

// MARK: - Declaration order in the source grammar must not matter

@Test func lexicalDefinition_declaredAfterItsUsage_stillResolves() throws {
    // The `lexical { }` block for `Identifier` appears *after* the production
    // that references it - this only works because tokens are collected in a
    // dedicated first pass before any production is rewritten.
    let syntax = BnfExpression.syntax([
        .production("primary", .nonterminal("Identifier")),
        .regex("Identifier", "[a-zA-Z]+"),
    ])

    let (productions, _, _, _, tokens) = StandardNotation().rewriteToStandardNotation(syntax: syntax)

    let rule = try #require(productions.first?.rule)
    #expect(rule == [.terminal(try #require(tokens["Identifier"]))])
}

// MARK: - Mixed alternatives: only the branches naming a lexical identifier are rewritten

@Test func alternative_mixingLexicalAndOrdinaryReferences_rewritesOnlyMatchingBranches() {
    let syntax = BnfExpression.syntax([
        .regex("Identifier", "[a-zA-Z]+"),
        .regex("Number", "[0-9]+"),
        .production("primary", .alternative([
            .nonterminal("Identifier"),
            .nonterminal("Number"),
            .nonterminal("group"),
        ])),
        .production("group", .terminal("(")),
    ])

    let (productions, _, _, _, _) = StandardNotation().rewriteToStandardNotation(syntax: syntax)
    let primaryProductions = productions.filter { $0.goal == NonTerminal(name: "primary") }

    #expect(primaryProductions.count == 3)
    #expect(primaryProductions[0].rule.first?.isTerminal == true)     // Identifier
    #expect(primaryProductions[1].rule.first?.isTerminal == true)     // Number
    #expect(primaryProductions[2].rule.first?.isNonTerminal == true)  // group (a real production)
}

// MARK: - A production sharing a name with a lexical definition: lexical wins

@Test func lexicalDefinition_takesPrecedenceOverSameNamedProduction() {
    let syntax = BnfExpression.syntax([
        .regex("Identifier", "[a-zA-Z]+"),
        .production("Identifier", .terminal("shouldNotWin")),
        .production("primary", .nonterminal("Identifier")),
    ])

    let (productions, _, _, _, tokens) = StandardNotation().rewriteToStandardNotation(syntax: syntax)
    let primary = productions.first { $0.goal == NonTerminal(name: "primary") }

    #expect(primary?.rule == [.terminal(tokens["Identifier"]!)])
}

// MARK: - End-to-end: Grammar carries the resolved lexical tokens through

@Test func grammar_carriesLexicalTokens_andIncludesThemAsGeneratedTerminals() throws {
    let syntax = BnfExpression.syntax([
        .regex("Identifier", "[a-zA-Z]+"),
        .production("primary", .nonterminal("Identifier")),
    ])

    let (productions, nonTerminals, _, _, tokens) = StandardNotation().rewriteToStandardNotation(syntax: syntax)
    let grammar = Grammar(productions: productions, start: NonTerminal(name: "primary"), lexicalTokens: tokens)

    let identifierTerminal = try #require(tokens["Identifier"])
    #expect(grammar.lexicalTokens["Identifier"] == identifierTerminal)
    #expect(grammar.terminals.contains(identifierTerminal))
    #expect(nonTerminals.isEmpty) // no synthetic non-terminals were needed here
}
