import Foundation
import Testing
@testable import Grammar

private final class RecordingGrammarLogSink: GrammarLogSink, @unchecked Sendable {
    private let lock = NSLock()
    private var storage: [GrammarLogEvent] = []

    func record(_ event: GrammarLogEvent) {
        lock.lock()
        storage.append(event)
        lock.unlock()
    }

    var events: [GrammarLogEvent] {
        lock.lock()
        defer { lock.unlock() }
        return storage
    }
}

@Test func loggingDefaultsToNoOperationAndEventsRoundTrip() throws {
    GrammarLogging.disabled.information("ignored", category: .grammar)

    let event = GrammarLogEvent(
        level: .trace, category: .parser, message: "production detected"
    )
    let encoded = try JSONEncoder().encode(event)

    #expect(try JSONDecoder().decode(GrammarLogEvent.self, from: encoded) == event)
}

@Test func parserPublishesStructuredEventsToInjectedSink() {
    let sink = RecordingGrammarLogSink()
    let parser = GrammarParser(
        grammar: "expression = 'number'\nterm = 'identifier'",
        logging: GrammarLogging(sink: sink)
    )

    _ = parser.parse()

    #expect(!sink.events.isEmpty)
    #expect(sink.events.allSatisfy { $0.category == .parser })
    #expect(sink.events.allSatisfy { $0.level == .trace })
}

@Test func grammarTransformationsPublishStructuredEventsToInjectedSink() {
    let sink = RecordingGrammarLogSink()
    let start = NonTerminal(name: "expression")
    let grammar = Grammar(
        productions: [.init(goal: start, rule: [
            .metaSymbol(.lbracket), .terminal("number"), .metaSymbol(.rbracket)
        ])],
        start: start,
        lexicalTokens: [:]
    )

    _ = grammar.rewriteToStandardForm(logging: GrammarLogging(sink: sink))

    #expect(sink.events.contains { $0.category == .grammar && $0.level == .information })
}
