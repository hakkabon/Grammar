# Grammar

A Swift package for constructing, analysing, transforming, and pretty-printing **Context-Free Grammars (CFGs)**. It covers the full lifecycle of a grammar: from parsing a textual notation (BNF, EBNF, WSN) into a structured representation, through analysis and normalisation, to generating railroad diagrams.

[![Swift 5.9+](https://img.shields.io/badge/Swift-5.9%2B-orange.svg)](https://swift.org)  
[![Platforms](https://img.shields.io/badge/platforms-macOS%2011%20%7C%20iOS%2014-blue.svg)](https://developer.apple.com/swift/)  
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)  

---

## Table of Contents

- [Overview](#overview)
- [Core Types](#core-types)
- [Package Structure](#package-structure)
- [Getting Started](#getting-started)
- [Subdirectory Reference](#subdirectory-reference)
- [References](#references)
- [Installation](#installationb)
- [License](#license)

---

## Overview

A **context-free grammar** is defined by the tuple G = (V, T, P, S):

| Component | Description |
|---|---|
| V | Set of non-terminal symbols |
| T | Set of terminal symbols |
| P | Set of production rules P: N → (N ∪ T)* |
| S | Start symbol |

The `Grammar` struct captures all four components and provides a rich API for working with grammars programmatically.

```swift
// Build a grammar in code
let grammar = Grammar(productions: [
    Production(goal: "E", rule: [n("E"), t("+"), n("T")]),
    Production(goal: "E", rule: [n("T")]),
    Production(goal: "T", rule: [t("n")]),
], start: "E", lexicalTokens: [:])

// Or parse it from a WSN string
let grammar = try Grammar(wsn: """
    E : E '+' T | T
    T : 'n'
""", start: "E")

// Or from BNF
let grammar = try Grammar(bnf: """
    <E> ::= <E> '+' <T> | <T>
    <T> ::= 'n'
""", start: "E")
```

---

## Core Types

### `Grammar`  (`Grammar.swift`)

The central struct. Holds productions, the start symbol, epsilon and EOF markers, and nullable non-terminals computed at initialisation. Provides:

- String output in BNF, EBNF, and WSN notation via `.bnf`, `.ebnf`, `.wsn`
- Computed sets of all non-terminals and terminals
- A `grammarForm` property that triggers normalisation when set (standard, Chomsky, Greibach)
- Initialisers for programmatic construction and for parsing BNF / EBNF / WSN strings
- `Equatable` and `Codable` conformance

### `Production`  (`Production.swift`)

A single production rule `A → α`. Immutable value type holding:

- `goal: NonTerminal` — the left-hand side
- `rule: [Symbol]` — the right-hand side as an ordered list of symbols

Key computed properties: `isFinal`, `isInChomskyNormalForm`, `isNullable`, `generatedTerminals`, `generatedNonTerminals`, `containsSymbol(_:)`.

### `GrammarVocabulary`  (`GrammarVocabulary.swift`)

A protocol a grammar implements to describe its own lexical vocabulary —
exact keywords and symbols, regex patterns, and which of those should be
scanned but hidden from the parser (whitespace, comments):

```swift
public protocol GrammarVocabulary {
    var keywords: [String: AnyHashable] { get }
    var symbols: [String: AnyHashable] { get }
    var patterns: [String: AnyHashable] { get }
    var skippedTypes: Set<AnyHashable> { get }
}
```

`Grammar` itself has no lexer dependency and does nothing with this protocol
beyond declaring it — it's consumed by
[Lexer](https://github.com/hakkabon/Lexer)'s
`LexerBuilder.loadVocabulary(_:)`, which bootstraps a working DFA lexer from
any conforming type, automatically resolving the keyword-vs-identifier
priority problem (see that module's README for the full rationale). See
[§7](#7--bootstrapping-a-lexer-from-a-grammarvocabulary) below.

---

## Package Structure

```
Sources/Grammar/
├── Grammar.swift                 Core Grammar struct
├── Production.swift              Production rule type
├── GrammarVocabulary.swift       Protocol for bootstrapping a lexer from keywords/symbols/patterns
├── GrammarLogger.swift           OSLog category definitions
│
├── Symbols/                      The symbol type hierarchy
│   ├── Symbol.swift              Enum: .terminal | .nonTerminal | .metaSymbol
│   ├── Terminal.swift            Terminal: string, regex, character range, meta
│   ├── NonTerminal.swift         Non-terminal name wrapper
│   ├── MetaTerminal.swift        Boundary markers: ε, λ, $, ¶
│   ├── MetaSymbol.swift          EBNF structure markers: { } [ ] ( ) |
│   ├── Symbols.swift             Factory helpers: t(), n(), rt(), mt(), ms()
│   └── SymbolSet.swift           Pre-built symbol sets (letters, digits, …)
│
├── GrammarImport/                Parsing grammars from text
│   ├── BNFGrammar.swift          Grammar(bnf:start:)
│   ├── EBNFGrammar.swift         Grammar(ebnf:start:)
│   ├── WSNGrammar.swift          Grammar(wsn:start:)
│   └── GenericGrammar.swift      Grammar(gen:) — Jones generic notation
│
├── GrammarParser/                Recursive-descent grammar parser
│   ├── GrammarParser.swift       Tokenizer-driven parser producing BnfExpression
│   ├── GrammarExpression.swift   BnfExpression AST node type
│   ├── GrammarDiagnostics.swift  Error reporting with source location
│   ├── GrammarPrettyPrinter.swift Re-formats BnfExpression back to text
│   ├── GrammarDocumenter.swift   Combines pretty-print + railroad diagram
│   └── GrammarRailroad.swift     Converts BnfExpression to ASCII railroad diagrams
│
├── GrammarNotation/              EBNF → BNF rewriting
│   ├── StandardNotation.swift    Rewrites a parsed syntax tree to flat BNF productions
│   └── StandardForm.swift        Transforms meta-symbols ( {} [] () | ) to BNF
│
├── GrammarBuilder/               Swift DSL for programmatic grammar construction
│   ├── GrammarBuilders.swift     @GrammarBuilder, @GrammarRuleBuilder result builders
│   ├── RuleBuilder.swift         Rule, Cat, Alt, Seq, Grp, Opt wrapper types
│   ├── ProductionResult.swift    <+> <|> --> operators for production assembly
│   └── ProductionBuilder.swift   (legacy) @ProductionBuilder
│
├── GrammarAnalysis/              Static analysis algorithms
│   ├── FirstFollow.swift         FIRST/FOLLOW sets, isLL1 check
│   ├── Nullable.swift            Nullable non-terminal computation
│   ├── LeftFactoring.swift       Left-factoring (Dragon Book Algorithm 4.21)
│   ├── LeftRecursion.swift       Left-recursion elimination (Dragon Book Algorithm 4.19)
│   ├── CycleDetection.swift      DFS-based cycle detection
│   └── Hygiene.swift             Unreachable / undefined / unit-rule elimination
│
├── GrammarForms/                 Grammar normal-form conversions
│   ├── GrammarForms.swift        isInChomskyNormalForm, isInGreilbachForm properties
│   ├── ChomskyForm.swift         toChomskyNormalForm() — four-step CNF algorithm
│   └── GreilbachForm.swift       toGreibachNormalForm() — six-step GNF algorithm
│
├── GrammarFuzzer/                Random string generation from a grammar
│   ├── GrammarFuzzer.swift       Protocol / base class for fuzzers
│   ├── SimpleGrammarFuzzer.swift Simple random derivation
│   └── DerivationNode.swift      Node in a derivation tree
│
├── ADTs/                         General-purpose data structures
│   ├── Stack.swift               Value-type LIFO stack
│   ├── Queue.swift               Reference-type FIFO queue
│   └── MutableList.swift         Reference-type random-access list
│
├── Extensions/                   Standard library extensions
│   ├── Character+Extensions.swift  Character Codable conformance
│   ├── Collection+Extensions.swift longestCommonPrefix / longestCommonSuffix
│   ├── Sequence+Extensions.swift   unique, strided, pairs, prefixes, combinations, …
│   └── String+Extensions.swift     Regex helpers, Terminal prefix matching, escaping
│
└── Utils/                        Small utilities
    ├── Counter.swift             Thread-safe monotonic counter
    ├── Either.swift              Generic Either<A,B> enum
    ├── Modulus.swift             Signed modulus mod(_:with:)
    └── Sequence.swift            Cartesian product, crossMap, unzip
```

---

## Getting Started

### 1 — Parsing a grammar from text

```swift
// Wirth Syntax Notation
let grammar = try Grammar(wsn: """
    E  : T Ex
    Ex : '+' T Ex | ε
    T  : F Tx
    Tx : '*' F Tx | ε
    F  : '(' E ')' | 'id'
""", start: "E")

// BNF with angle brackets
let grammar = try Grammar(bnf: """
    <expr> ::= <expr> '+' <term> | <term>
    <term> ::= 'n'
""", start: "expr")

// EBNF
let grammar = try Grammar(ebnf: """
    expr = term { '+' term } ;
    term = 'n' ;
""", start: "expr")
```

### 2 — Building a grammar in Swift code

```swift
// Using the @GrammarBuilder DSL
let grammar = Grammar(start: "S") {
    Production(goal: "S", rule: [n("A"), n("B")])
    Production(goal: "A", rule: [t("a")])
    Production(goal: "B", rule: [t("b")])
}

// Using the operator DSL
let S: NonTerminal = "S"
let A: NonTerminal = "A"
let productions = (S --> n("A") <+> n("B"))
                + (A --> t("a"))
```

### 3 — Normalisation to Standard Form (BNF)

EBNF constructs `{ }`, `[ ]`, `( )`, `|` are eliminated automatically:

```swift
let (flatProductions, generatedNTs) = grammar.rewriteToStandardForm()
let standardGrammar = Grammar(productions: flatProductions, start: grammar.start, lexicalTokens: [:])
```

### 4 — Analysis

```swift
let (firstSets, followSets) = standardGrammar.firstAndFollow()

let cycles = standardGrammar.detectCycles()

let leftFactored = standardGrammar.leftFactoring()

let noLeftRecursion = standardGrammar.eliminateLeftRecursion()

let nullables = standardGrammar.allNullableNonTerminals()

let undefinedNTs = standardGrammar.undefinedNonterminals
```

### 5 — Normal form conversion

```swift
// Chomsky Normal Form  (A → a  or  A → B C)
let cnf = grammar.toChomskyNormalForm()
print(cnf.isInChomskyNormalForm)   // true

// Greibach Normal Form  (A → a α where α ∈ V*)
let gnf = grammar.toGreibachNormalForm()
print(gnf.isInGreilbachForm)       // true
```

### 6 — String output

```swift
print(grammar.bnf)   // <E> ::= <E> '+' <T> | <T>
print(grammar.ebnf)  // E ::= E , "+" , T | T
print(grammar.wsn)   // E = E '+' T | T
```

### 7 — Bootstrapping a lexer from a `GrammarVocabulary`

```swift
import Grammar
import Lexer

struct ArithmeticVocabulary: GrammarVocabulary {
    enum Tag { case number, plus, times, lparen, rparen }

    let keywords: [String: AnyHashable] = [:]
    let symbols: [String: AnyHashable] = ["+": Tag.plus, "*": Tag.times, "(": Tag.lparen, ")": Tag.rparen]
    let patterns: [String: AnyHashable] = ["[0-9]+": Tag.number]
    let skippedTypes: Set<AnyHashable> = []
}

var builder = LexerBuilder()
builder.loadVocabulary(ArithmeticVocabulary())
let lexer = try builder.build()

let stream = try LexerTokenStream(source: "1 + 2 * 3", lexer: lexer)
let result = try parser.parse(stream: stream)
```

See [Lexer](https://github.com/hakkabon/Lexer)'s README for the full
`TokenStream` design (including the fixed-category `TokenizerStream`
alternative built on GrammarTokenizer) and the priority/quoting rationale
behind `loadVocabulary(_:)`.

---

## Subdirectory Reference

### `Symbols/` — The symbol type hierarchy

Every symbol in a grammar rule is a `Symbol`, an enum with three cases:

```
Symbol
├── .terminal(Terminal)
│   ├── .string(String)               — plain quoted string
│   ├── .characterRange(ClosedRange)  — 'a'...'z'
│   ├── .regularExpression(NSRegularExpression)
│   └── .meta(MetaTerminal)           — ε  λ  $  ¶  ""
├── .nonTerminal(NonTerminal)          — named, Hashable, Comparable
└── .metaSymbol(MetaSymbol)            — { } [ ] ( ) | — EBNF structural markers
```

`MetaSymbol`s appear only before standard-form rewriting. `MetaTerminal`s (ε, $) survive into the final grammar and drive nullable and FIRST/FOLLOW computations.

Factory functions in `Symbols.swift` reduce boilerplate: `t("a")`, `n("S")`, `rt("[0-9]+")`, `mt("ε")`.

### `GrammarImport/` — Parsing from text

Three parsers share the same `GrammarParser` tokenizer back-end and `StandardNotation` rewriter:

| Initialiser | Notation | Non-terminal syntax | Definition | Separator |
|---|---|---|---|---|
| `Grammar(bnf:start:)` | BNF | `<name>` | `::=` | newline / `;` |
| `Grammar(ebnf:start:)` | EBNF | `name` | `=` | `;` or `.` |
| `Grammar(wsn:start:)` | WSN | `name` | `=` | `.` or `;` |
| `Grammar(gen:)` | Generic | `<name>` or `name` | `:` `=` `::=` | optional |

All four accept the same richly extended syntax including `{ }` repetition, `[ ]` option, `( )` grouping, regular expressions inside a `lexical { }` block, and multi-line comments.

### `GrammarParser/` — The recursive-descent parser

`GrammarParser` drives a `Tokenizer` (from the `GrammarTokenizer` package dependency) and produces a `BnfExpression` AST. The parser understands both BNF (`<ident> ::=`) and EBNF/WSN (`ident =`) notation, detects which style is in use, and recovers from syntax errors using panic-mode synchronisation.

`BnfExpression` is an indirect enum covering: `.syntax`, `.production`, `.sequence`, `.alternative`, `.optional`, `.repetition`, `.repetitionOnePlus`, `.grouping`, `.terminal`, `.nonterminal`, `.range`, `.list`, `.regex`, `.emptyStringSymbol`, `.startSymbol`.

`GrammarPrettyPrinter` re-serialises any `BnfExpression` back to a human-readable string, and `GrammarToRailroad` converts it to ASCII railroad diagrams (via the `GrammarDiagram` package).

### `GrammarNotation/` — EBNF → BNF rewriting

Two complementary rewriters flatten a grammar to Standard BNF:

- **`StandardNotation`** — rewrites a parsed `BnfExpression` syntax tree into a flat `[Production]` list. Handles `{ }`, `[ ]`, `( )`, and nested alternatives by introducing fresh synthetic non-terminals.
- **`StandardForm`** — rewrites productions that still contain `MetaSymbol` values (the raw bracket tokens from the symbol stream) into pure BNF, using the classical algorithms: `reduceGroupings`, `reduceOptions`, `reduceRepetitions`, `rewriteAlternations`.

### `GrammarBuilder/` — Swift DSL

Two DSL layers for writing grammars directly in Swift:

**Operator DSL** (`ProductionResult.swift`) — concise but lower-level:
```swift
"S" --> n("A") <+> n("B")
"S" --> t("a") <|> t("b")
```

**Result-builder DSL** (`RuleBuilder.swift`, `GrammarBuilders.swift`) — reads like the grammar itself:
```swift
Grammar(start: "S") {
    Rule("S") { Alt { n("A") ; n("B") } }
    Rule("A") { t("a") }
}
```
The `Cat`, `Alt`, `Seq`, `Grp`, and `Opt` types map directly to concatenation, alternation, zero-or-more repetition, grouping, and option.

### `GrammarAnalysis/` — Static analysis

| File | Algorithm | Public API |
|---|---|---|
| `FirstFollow.swift` | Fixed-point FIRST and FOLLOW | `firstAndFollow()`, `first(of:using:)`, `followSets()`, `isLL1(first:follow:)` |
| `Nullable.swift` | Nullable non-terminal set | `allNullableNonTerminals()`, `isNullable(_:)` |
| `LeftFactoring.swift` | Dragon Book Algorithm 4.21 | `leftFactoring() -> [Production]` |
| `LeftRecursion.swift` | Dragon Book Algorithm 4.19 | `eliminateLeftRecursion() -> [Production]` |
| `CycleDetection.swift` | DFS cycle detection | `detectCycles() -> [[Symbol]]` |
| `Hygiene.swift` | Reachability / unit-rule elimination | `unreachableNonTerminals`, `undefinedNonterminals`, `eliminateUnusedProductions`, `eliminateUnitRules`, `eliminateEmpty` |

### `GrammarForms/` — Normal-form conversions

**Chomsky Normal Form** (`ChomskyForm.swift`):  
Every production becomes either `A → a` (single terminal) or `A → B C` (two non-terminals). Four steps: ε-elimination → unit-production elimination → TERM (terminal wrapping) → BIN (binarisation).

**Greibach Normal Form** (`GreilbachForm.swift`):  
Every production becomes `A → a α` where `a` is a terminal and `α` is a (possibly empty) sequence of non-terminals. Six steps: ε-elimination → unit elimination → left-recursion elimination (Rosenkrantz–Stearns) → back-substitution → tail-terminal wrapping.

### `GrammarFuzzer/` — Grammar-based fuzzing

`GrammarFuzzer` and `SimpleGrammarFuzzer` generate random strings from a grammar by repeatedly expanding non-terminals. Derivation steps are captured in `DerivationNode` trees, allowing the full derivation history to be inspected.

### `ADTs/` — Data structures

- `Stack<T>` — value-type LIFO stack with `push`, `pop`, `top`
- `Queue<T>` — reference-type FIFO queue with amortised O(1) dequeue
- `List<T>` / `MutableList<T>` — reference-type array wrapper with functional collection operations

### `Extensions/` — Standard library additions

- `String` — regex matching helpers, `Terminal`-based prefix detection, literal escaping
- `Sequence` — `unique(by:)`, `strided`, `pairs`, `prefixes`, `combinations`, `partition`, `collect`
- `Collection` — `longestCommonPrefix`, `longestCommonSuffix` on `StringProtocol` sequences
- `Character` — `Codable` conformance

### `Utils/` — Small utilities

- `Counter` — global thread-safe monotonic integer counter used for generating unique non-terminal names
- `Either<A,B>` — generic sum type with `map` and `combine`
- `mod(_:with:)` — correct signed modulus (handles negative divisors)
- Sequence operations: `crossProduct`, `crossMap`, `crossFlatMap`, `unzip`

---

## Dependencies

| Package | Purpose |
|---|---|
| `GrammarTokenizer` | Tokeniser used by `GrammarParser` |
| `GrammarDiagram` | ASCII railroad diagram rendering |
| `TerminalColors` | ANSI colour output for diagnostics and tree printing |
| `swift-algorithms` | `uniqued()` used in `Grammar.givenOrder` |
| `swift-argument-parser` | Used by the `bnf` executable target |

---

## References

1. Parsing Techniques, A Practical Guide, 2nd Edition  
Dick Grune, Ceriel J.H. Jacobs,  
Springer Publishing Company 2008  
 
2. Compilers: Principles, Techniques, and Tools, 2nd Edition  
by Alfred V. Aho, Ravi Sethi, and Jeffrey D. Ullman  
Addison Wesley 2007  

3. Crafting a compiler  
by Charles N., Cytron, Ron K., LeBlanc Jr., Richard J Fischer  
Pearson 2009  
 
4. Automata, Computability and Complexity - Theory and Applications  
by Elaine Rich  
Pearson Education Inc. 2007  

---

## Installation
Add this package to your Swift project using the Swift Package Manager.

Add to your Package.swift:  
```swift
dependencies: [
    .package(name: "Grammar", url: "https://github.com/hakkabon/Grammar", branch: "main"),
],
targets: [
    .target(
        name: "MyTarget", 
        dependencies: [
            .product(name: "Grammar", package: "Grammar"),
        ]
    ),
]
```

---

## License

MIT License — see [LICENSE](LICENSE) for details.  

