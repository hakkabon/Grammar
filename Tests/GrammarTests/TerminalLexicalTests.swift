import Foundation
import Testing
@testable import Grammar

// MARK: - Terminal.stringList construction & equality

@Test func terminal_stringList_matchesContainedString() {
    let list = Terminal(list: ["true", "false"])
    #expect(list == Terminal(string: "true"))
    #expect(Terminal(string: "false") == list)
    #expect(list != Terminal(string: "maybe"))
}

@Test func terminal_stringList_equality() {
    #expect(Terminal(list: ["a", "b"]) == Terminal(list: ["a", "b"]))
    // Symbol.== on the underlying [String] is order-sensitive, matching Array's own ==.
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

// MARK: - Terminal.characterRange <-> .string cross-matching

@Test func terminal_characterRange_matchesSingleCharacterString() {
    let digit = Terminal(range: "0" ... "9")
    #expect(digit == Terminal(string: "5"))
    #expect(Terminal(string: "5") == digit)
}

@Test func terminal_characterRange_rejectsOutOfRangeOrMultiCharacterString() {
    let digit = Terminal(range: "0" ... "9")
    #expect(digit != Terminal(string: "x"))
    #expect(digit != Terminal(string: "55"))
}
