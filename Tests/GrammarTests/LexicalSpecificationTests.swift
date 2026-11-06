import Foundation
import Testing
@testable import Grammar

@Suite("Unified lexical specification")
struct LexicalSpecificationTests {
    private let source = #"""
    lexical {
        keyword BEGIN = "begin";
        token IDENTIFIER = /[A-Za-z_][A-Za-z0-9_]*/;
        symbol ASSIGN = ":=";
        trivia WHITESPACE = /\s+/;
        trivia LINE_COMMENT = lineComment("//");
        trivia BLOCK_COMMENT = blockComment("/*", "*/");
    }
    Program ::= BEGIN IDENTIFIER ASSIGN IDENTIFIER;
    """#

    @Test func grammarParserPublishesOrderedLexerRules() {
        let parser = GrammarParser(grammar: source)
        _ = parser.parse()

        #expect(parser.diagnostics.isEmpty)
        #expect(parser.lexicalSpecification.rules.map(\.name) == [
            "BEGIN", "IDENTIFIER", "ASSIGN", "WHITESPACE",
            "LINE_COMMENT", "BLOCK_COMMENT",
        ])
        #expect(parser.lexicalSpecification["BEGIN"]?.matcher == .literal("begin"))
        #expect(parser.lexicalSpecification["WHITESPACE"]?.channel == .trivia)
        #expect(parser.lexicalSpecification["LINE_COMMENT"]?.matcher == .lineComment("//"))
        #expect(parser.lexicalSpecification["BLOCK_COMMENT"]?.matcher
            == .blockComment(open: "/*", close: "*/"))
    }

    @Test func grammarImportRetainsTheSameLexicalArtifact() throws {
        let grammar = try Grammar(bnf: source, start: "Program")

        #expect(grammar.lexicalSpecification.rules.count == 6)
        #expect(grammar.productions.count == 1)
        #expect(grammar.productions[0].rule.count == 4)
    }

    @Test func legacyGrammarArtifactDecodesWithoutLexicalSpecification() throws {
        let grammar = try Grammar(bnf: source, start: "Program")
        let encoded = try JSONEncoder().encode(grammar)
        var object = try #require(
            JSONSerialization.jsonObject(with: encoded) as? [String: Any])
        object.removeValue(forKey: "lexicalSpecification")

        let legacyData = try JSONSerialization.data(withJSONObject: object)
        let decoded = try JSONDecoder().decode(Grammar.self, from: legacyData)

        #expect(decoded.lexicalSpecification == .empty)
        #expect(decoded.productions == grammar.productions)
    }
}
