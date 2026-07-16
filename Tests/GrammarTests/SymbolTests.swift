import Testing
@testable import Grammar

// MARK: - Symbol helper tests

@Test func symbol_isTerminal() {
    #expect(t("a").isTerminal == true)
    #expect(n("A").isTerminal == false)
    #expect(ms("{").isTerminal == false)
}

@Test func symbol_isNonTerminal() {
    #expect(n("A").isNonTerminal == true)
    #expect(t("a").isNonTerminal == false)
    #expect(ms("{").isNonTerminal == false)
}

@Test func symbol_isEpsilon_epsMeta() {
    let epsSym = Symbol.terminal(.meta(.eps))
    #expect(epsSym.isEpsilon == true)
}

@Test func symbol_isEpsilon_emptyString() {
    #expect(t("").isEpsilon == true)
}

@Test func symbol_isEpsilon_nonEps() {
    #expect(t("a").isEpsilon == false)
    #expect(n("A").isEpsilon == false)
}

@Test func symbol_nonTerminalAccessor() {
    let sym = n("E")
    #expect(sym.nonTerminal == NonTerminal(name: "E"))
    #expect(t("a").nonTerminal == nil)
}

@Test func symbol_terminalAccessor() {
    let sym = t("a")
    #expect(sym.terminal == Terminal(string: "a"))
    #expect(n("A").terminal == nil)
}

@Test func symbol_equality() {
    #expect(t("a") == t("a"))
    #expect(t("a") != t("b"))
    #expect(n("A") == n("A"))
    #expect(n("A") != n("B"))
    #expect(t("a") != n("a"))
}

@Test func symbolArray_isNullable_empty() {
    let arr: [Symbol] = []
    #expect(arr.isNullable == true)
}

@Test func symbolArray_isNullable_allEpsilon() {
    let arr: [Symbol] = [t(""), t("")]
    #expect(arr.isNullable == true)
}

@Test func symbolArray_isNullable_withNonTerminal() {
    let arr: [Symbol] = [n("A")]
    #expect(arr.isNullable == false)
}

@Test func symbolArray_hasPrefix_true() {
    let arr: [Symbol] = [t("a"), t("b"), t("c")]
    #expect(arr.hasPrefix([t("a"), t("b")]) == true)
}

@Test func symbolArray_hasPrefix_false() {
    let arr: [Symbol] = [t("a"), t("b")]
    #expect(arr.hasPrefix([t("a"), t("b"), t("c")]) == false)
    #expect(arr.hasPrefix([t("b")]) == false)
}

@Test func symbolArray_commonPrefix() {
    let arr1: [Symbol] = [t("a"), t("b"), t("c")]
    let arr2: [Symbol] = [t("a"), t("b"), t("d")]
    let prefix = arr1.commonPrefix(with: arr2)
    #expect(prefix == [t("a"), t("b")])
}

@Test func nonTerminal_expressibleByStringLiteral() {
    let nt: NonTerminal = "E"
    #expect(nt.name == "E")
}

@Test func nonTerminal_comparableOrdering() {
    let a = NonTerminal(name: "A")
    let b = NonTerminal(name: "B")
    #expect(a < b)
    #expect(b > a)
}

@Test func terminal_isEmpty_string() {
    #expect(Terminal(string: "").isEmpty == true)
    #expect(Terminal(string: "a").isEmpty == false)
}

@Test func terminal_isEmpty_metaEps() {
    #expect(Terminal.meta(.eps).isEmpty == true)
    #expect(Terminal.meta(.eof).isEmpty == false)
}

@Test func terminal_RegexMatchString() {
    let regexTerminal = try! Terminal(expression: "[a-z]+")
    let stringTerminal = Terminal(string: "abc")
    // String matching regex should be true
    #expect(regexTerminal.matches(stringTerminal))
}

@Test func terminal_expressibleByStringLiteral() {
    let t: Terminal = "hello"
    #expect(t == Terminal(string: "hello"))
}

@Test func symbolSet_staticSets() {
    #expect(SymbolSet.numbers.symbols.count == 10)
    #expect(SymbolSet.lowercase.symbols.count == 26)
    #expect(SymbolSet.uppercase.symbols.count == 26)
    #expect(SymbolSet.letters.symbols.count == 52)
    #expect(SymbolSet.alphanumerics.symbols.count == 62)
}
