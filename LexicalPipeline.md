# Grammar and lexical pipeline

A language grammar is the single source for both productions and lexical
rules. `GrammarTokenizer` reads the notation, `GrammarParser` creates the
syntax tree and ordered `LexicalSpecification`, and `StandardNotation` lowers
the productions for parser engines.

```bnf
> Program

lexical {
    keyword BEGIN = insensitive("begin");
    token IDENTIFIER = /[A-Za-z_][A-Za-z0-9_]*/;
    symbol ASSIGN = ":=";
    trivia WHITESPACE = /\s+/;
    trivia LINE_COMMENT = lineComment("//");
    trivia BLOCK_COMMENT = blockComment("/*", "*/");
}

Program ::= BEGIN IDENTIFIER ASSIGN IDENTIFIER;
```

The four declarators establish stable priority and channel semantics:

- `keyword` is a significant literal with priority 0.
- `symbol` is a significant literal with priority 1.
- `token` is a significant pattern with priority 2.
- `trivia` is retained losslessly but omitted from parser input.

Maximal munch wins first; priority and declaration order resolve equal-length
matches. Structured comment rules avoid regex assertions and allow scanners to
report unterminated comments precisely.

`insensitive("...")` is an explicit literal matcher for languages such as
Pascal. It remains readable, participates in the same keyword priority rules,
and does not require a duplicated language-specific keyword table.

`Lexer.GrammarDrivenLexer` consumes the specification directly. It publishes
UTF-16 ranges, significant tokens, retained trivia, and diagnostics, and it
conforms to `RestartableLexer`. `GrammarIncrementalTokenizer` therefore adds
restart-and-converge reuse without a language-specific scanner adapter.

## Language-kit rule

A language kit should contain its grammar resource, typed projections,
semantics, formatting, and optional compiler services. It should not contain a
second grammar-definition parser, handwritten copies of declared lexical
rules, or its own restart-and-converge algorithm. A necessary exception must
be documented as a missing shared capability and covered by differential tests.

PL/0 is the reference conformance fixture for this rule. New kits, including
Pascal, should begin with the same pipeline.
