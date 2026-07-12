import Foundation
import Testing
@testable import Grammar

// MARK: - Terminal.stringList construction & structural equality

@Test func terminal_stringList_equality() {
    #expect(Terminal(list: ["a", "b"]) == Terminal(list: ["a", "b"]))
    // == on the underlying [String] is order-sensitive, matching Array's own ==.
    #expect(Terminal(list: ["a", "b"]) != Terminal(list: ["b", "a"]))
}

@Test func terminal_stringList_isEmpty() {
    #expect(Terminal(list: []).isEmpty == true)
    #expect(Terminal(list: [""]).isEmpty == true)
    #expect(Terminal(list: ["a", ""]).isEmpty == false)
}

@Test func terminal_stringList_hashableUsableInSet() {
    let terminals: Set<Terminal> = [Terminal(list: ["x", "y"]), Terminal(list: ["x", "y"])]
    #expect(terminals.count == 1)
}

@Test func terminal_stringList_codableRoundTrip() throws {
    let original = Terminal(list: ["one", "two", "three"])
    let data = try JSONEncoder().encode(original)
    let decoded = try JSONDecoder().decode(Terminal.self, from: data)
    #expect(decoded == original)

    guard case .stringList(let list) = decoded else {
        Issue.record("Expected .stringList after decoding, got \(decoded)")
        return
    }
    #expect(list == ["one", "two", "three"])
}

// MARK: - == is strict structural equality: no cross-case matching

@Test func terminal_equality_doesNotCrossMatchDifferentCases() throws {
    let digit = Terminal(range: "0" ... "9")
    let five = Terminal(string: "5")
    let digitRegex = try Terminal(expression: "[0-9]")

    #expect(digit != five)
    #expect(five != digitRegex)
    #expect(digit != digitRegex)
    #expect(Terminal(list: ["true", "false"]) != Terminal(string: "true"))
}

// Regression guard for the bug `matches(_:)` was split out to fix: under the
// old ==-based cross-matching, `a == b` and `b == c` could both be true while
// `a == c` was false, since there was no (.characterRange, .regularExpression)
// case - not a lawful equivalence relation. With == restricted to same-case
// comparison, none of these three are == to one another any more, and
// Set<Terminal>/[Terminal: _] (e.g. Grammar.terminals) can trust == again.
@Test func terminal_equality_isNowTransitive() throws {
    let a = Terminal(range: "0" ... "9")
    let b = Terminal(string: "5")
    let c = try Terminal(expression: "[0-9]")

    #expect(a != b)
    #expect(b != c)
    #expect(a != c)

    // The relationship these used to express now lives in matches(_:), which
    // makes no transitivity promise (and doesn't need to).
    #expect(a.matches(b))
    #expect(c.matches(b))
}

// MARK: - matches(_:): the asymmetric pattern-vs-token check for scan()

@Test func terminal_matches_characterRangeAcceptsSingleCharacterToken() {
    let digit = Terminal(range: "0" ... "9")
    #expect(digit.matches(Terminal(string: "5")))
    #expect(digit.matches(Terminal(string: "x")) == false)
    #expect(digit.matches(Terminal(string: "55")) == false) // not a single character
}

@Test func terminal_matches_regularExpressionAcceptsMatchingToken() throws {
    let identifier = try Terminal(expression: "[a-zA-Z]+")
    #expect(identifier.matches(Terminal(string: "abc")))
    #expect(identifier.matches(Terminal(string: "123")) == false)
}

@Test func terminal_matches_stringListAcceptsContainedToken() {
    let boolean = Terminal(list: ["true", "false"])
    #expect(boolean.matches(Terminal(string: "true")))
    #expect(boolean.matches(Terminal(string: "false")))
    #expect(boolean.matches(Terminal(string: "maybe")) == false)
}

@Test func terminal_matches_isNotSymmetric() {
    // The pattern side and the token side are not interchangeable: a plain
    // string is a valid token to match against a range, but a range is not
    // a token that could ever satisfy a string-as-pattern.
    let digit = Terminal(range: "0" ... "9")
    let five = Terminal(string: "5")

    #expect(digit.matches(five))
    #expect(five.matches(digit) == false)
}

@Test func terminal_matches_fallsBackToEqualityForSameCasePatterns() throws {
    // Comparing one grammar's terminal against another (rather than against a
    // concrete lexed token) falls back to strict same-case equality.
    let a = try Terminal(expression: "[0-9]+")
    let b = try Terminal(expression: "[0-9]+")
    let c = try Terminal(expression: "[a-z]+")

    #expect(a.matches(b))
    #expect(a.matches(c) == false)
}
