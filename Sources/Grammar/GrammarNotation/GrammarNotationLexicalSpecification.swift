/// The shared lossless lexical vocabulary for BNF, EBNF, WSN, and Grammar's
/// combined notation. GrammarTokenizer remains the authoritative parser input;
/// this specification lets incremental consumers use the same notation names
/// without defining a language-kit-local scanner.
public enum GrammarNotationLexicalSpecification {
    public static let shared = LexicalSpecification(rules: [
        .init(name: "WHITESPACE", matcher: .regularExpression(#"\s+"#), channel: .trivia),
        .init(name: "LINE_COMMENT", matcher: .lineComment("//"), channel: .trivia),
        .init(name: "HASH_COMMENT", matcher: .lineComment("#"), channel: .trivia),
        .init(name: "BLOCK_COMMENT", matcher: .blockComment(open: "/*", close: "*/"), channel: .trivia),
        .init(name: "PAREN_COMMENT", matcher: .blockComment(open: "(*", close: "*)"), channel: .trivia),
        .init(name: "REGEX", matcher: .regularExpression(#"/(?:\\.|[^/\\])*/"#)),
        .init(name: "LITERAL", matcher: .regularExpression(#"\"(?:\\.|[^\"\\])*\"|'(?:\\.|[^'\\])*'"#)),
        .init(name: "IDENTIFIER", matcher: .regularExpression(#"[A-Za-z_][A-Za-z0-9_-]*"#)),
        .init(name: "NUMBER", matcher: .regularExpression(#"[0-9]+"#)),
        .init(name: "DEFINE", matcher: .literals(["::=", ":=", "->", "="])),
        .init(name: "RANGE", matcher: .literal("..")),
        .init(name: "PUNCTUATION", matcher: .literals([
            "<", ">", "{", "}", "[", "]", "(", ")", "|", ";", ".",
            ",", ":", "+", "-", "*", "?", "/", "^", "_", "`", "~",
        ])),
    ])
}
