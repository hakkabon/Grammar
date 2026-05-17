import Testing
@testable import Grammar

@Test func testIdentifier() async throws {
    let expression = "[a-zA-Z][a-zA-Z0-9-_]*"
    let identifies = [
        "A",
        "a",
        "abba",
        "AbbA",
        "Abba"
    ]
    
    for identifer in identifies {
        #expect(identifer.matches(expression) == true)
    }
}

@Test func testTerminal() async throws {
    let terminal = try Terminal(expression: "[a-zA-Z][a-zA-Z0-9-_]*")
    let identifies = [
        "A",
        "a",
        "abba",
        "AbbA",
        "Abba"
    ]
    
    for identifer in identifies {
        if case let .regularExpression(expression) = terminal {
            #expect(identifer.matches(expression.pattern) == true)
        }
    }
}
