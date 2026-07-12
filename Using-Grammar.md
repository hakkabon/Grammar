# Using the Grammar Module for Parsing

This is a reference for every currently-viable way to go from "I have a grammar,
somehow" to "I have a `Grammar` value ready to hand to a parser." 

## 1. What this module does — and doesn't do

`Grammar` is the definition-and-normalization layer, not a recognizer. Nothing
in this repository turns an input *string* into a parse tree. The pipeline is:

```
                    ┌──────────────────────────────────────────────────┐
 text / Swift DSL → │ AST → flatten to [Production] → Grammar → (norm) │ → sibling parser package
                    └──────────────────────────────────────────────────┘
                              (this repo)                                (Earley-Parser, LL-Parsing,
                                                                            LR-Parsing, CYK-Parser,
                                                                            RNGLR-Parser, GLR, ...)
```

Every scenario in §3 ends at the same place: a `Grammar` value with a flat
`[Production]` array, ready to optionally be rewritten into a normal form
(§5) and then handed to whichever parser package actually consumes it (§6).

## 2. The core data model

Every scenario below bottoms out in the same four types:

| Type         | Shape                                                                                                                                                                       | Notes                                                                                                                                                                                                   |
| ------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Grammar`    | `productions: [Production]`, `start: NonTerminal`, `epsilon`/`endofile: MetaTerminal`, `lexicalTokens: [String: Terminal]`, `generatedNonTerminals`, `nullableNonTerminals` | Also exposes computed `nonTerminals`, `terminals`, `startProduction`, and `bnf`/`ebnf`/`wsn` string views for round-tripping/debugging.                                                                 |
| `Production` | `goal: NonTerminal`, `rule: [Symbol]`                                                                                                                                       | Epsilon is **always** `rule == []`, never an explicit epsilon symbol — every initializer normalizes this away. `rule.isEmpty` is the one reliable nullability test used everywhere else in the package. |
| `Symbol`     | `.terminal(Terminal)` \| `.nonTerminal(NonTerminal)` \| `.metaSymbol(MetaSymbol)`                                                                                           | What actually appears on the right-hand side of a production.                                                                                                                                           |
| `Terminal`   | `.string` \| `.characterRange` \| `.stringList` \| `.regularExpression` \| `.meta(MetaTerminal)`                                                                            | A compiled match rule — not just a pattern string.                                                                                                                                                      |

Two convenience layers exist for building these by hand: `NonTerminal` is
`ExpressibleByStringLiteral` (so `"A"` works anywhere a `NonTerminal` is
expected), and `Symbols.swift` provides free functions for building `Symbol`
values tersely: `t("+")`, `n("expr")`, `rt("[0-9]+")` (regex, throwing),
`ct("0"..."9")` (character range), `lt("true", "false")` (string list),
`mt("ε")` (meta-terminal), `ms("(")` (meta-symbol).

`Terminal` has two comparison operations for two different questions. `==` is
strict structural equality (same case, same payload) — lawful, and what
`Set<Terminal>`/`[Terminal: _]` (e.g. `Grammar.terminals`) rely on.
`pattern.matches(token)` is the asymmetric check a parser's `scan()` step
should use instead: does this terminal, as it appears in a grammar's
production (`self` — a `.regularExpression`, `.characterRange`, `.stringList`,
or plain `.string`), accept that already-scanned lexeme (`token` — ordinarily
a `.string`)? `pattern.matches(token)` and `token.matches(pattern)` can
disagree by design.

## 3. Seven ways to obtain a `Grammar`

### A. BNF text

```swift
let grammar = try Grammar(
    bnf: """
    <expr> ::= <expr> "+" <term> | <term>
    <term> ::= "0" | "1" | "2"
    """,
    start: "expr"
)
```

Routes through `GrammarParser` → `BnfExpression` → `StandardNotation`. Angle
brackets around non-terminals, `::=`, `|` alternation. This is the most
literal/traditional notation and the one most compiler textbooks use.

### B. EBNF text (ISO/IEC 14977-flavored)

```swift
let grammar = try Grammar(
    ebnf: """
    expr = term , { ("+" | "-") , term } ;
    term = digit ;
    digit = "0" | "1" | "2" ;
    """,
    start: "expr"
)
```

Adds `[ ]` optional, `{ }` repetition, `( )` grouping, and `,` for explicit
concatenation on top of BNF's alternatives. Prefer this over raw BNF whenever
the grammar has any repetition or optionality — it saves you from
hand-writing right-recursive helper rules.

### C. WSN text (Wirth Syntax Notation)

```swift
let grammar = try Grammar(
    wsn: """
    expr = term { ("+" | "-") term } .
    term = digit .
    digit = "0" | "1" | "2" .
    """,
    start: "expr"
)
```

Same expressive power as EBNF (`[ ]`, `{ }`, `( )`), lighter punctuation
(implicit concatenation, no commas, `.` terminates a rule instead of `;`).
**Before this session's patch this scenario didn't compile** — `init(wsn:start:)`
referenced a variable that had been discarded a few lines earlier. Fixed as
part of `grammarbuilder-dsl-fix.patch`.

### D. Generic (Jones) notation text

```swift
let grammar = try Grammar(gen: """
> expr
expr ::= term { ("+" | "-") term }
term ::= digit
digit ::= "0" | "1" | "2"
""")
```

A WSN/BNF hybrid that additionally accepts `:`, `=`, `:=`, or `::=` as the
definition operator, and lets the start symbol be declared *inside* the text
with a leading `> name` metarule — this is the only text scenario that
doesn't take a separate `start:` argument. Useful when the grammar text
itself is the single source of truth for what its start symbol is (e.g.
loaded from a file at runtime).

### E. Programmatic construction from `[Production]`

```swift
let grammar = Grammar(
    productions: [
        Production(goal: "expr", rule: [n("expr"), t("+"), n("term")]),
        Production(goal: "expr", rule: [n("term")]),
        Production(goal: "term", rule: [t("0")]),
    ],
    start: "expr",
    lexicalTokens: [:]
)
```

No parsing of any notation at all — you already have (or generated) fully
flattened `[Symbol]` rules and just want a `Grammar` wrapper around them
(nullability computation, `.bnf`/`.ebnf` rendering, etc.). This is what every
scenario above eventually calls internally.

### F. Swift DSL (`Rule` / `Cat` / `Alt` / `Seq` / `Grp` / `Opt`)

```swift
let grammar = Grammar(start: "expr") {
    Rule("expr") {
        Alt {
            Cat { n("expr"); t("+"); n("term") }
            n("term")
        }
    }
    Rule("term") { Alt { t("0"); t("1"); t("2") } }
}
```

An embedded, type-checked EBNF: `Cat` for concatenation, `Alt` for choice,
`Seq` for zero-or-more repetition, `Opt` for optionality, `Grp` for grouping.
Symbols are already fully resolved at the call site — `rt(...)`/`ct(...)`/`lt(...)`
build a compiled `Terminal` directly, with no separate lexical block needed.
Prefer this over scenario E whenever the grammar has any alternation / optionality / repetition — you get the synthetic non-terminal bookkeeping for free instead of writing it by hand.

### G. Raw `[Production]`-array builder

```swift
let grammar = Grammar(start: "expr") {
    Production(goal: "expr", rule: [n("term")])
    Production(goal: "term", rule: [t("0")])
}
```

A thin `@resultBuilder` accumulator around scenario E — useful only for
grouping an already-flat list of `Production` values into a trailing closure;
it does not offer `Alt`/`Opt`/`Seq`/`Grp` sugar. In almost every case scenario
F is what you actually want.

## 4. Lexical tokens: regex / range / list terminals

Text grammars (A–D) can declare non-BNF terminal shapes in a `lexical { }`
block:

```
lexical {
    Identifier ::= /[a-zA-Z_][a-zA-Z0-9_]*/
    Digit      ::= '0' .. '9'
    Bool       ::= "true" | "false"
}
```

Any later reference to `<Identifier>`, `<Digit>`, or `<Bool>` inside an
ordinary production is automatically resolved to the matching `Terminal`
(regex / character-range / string-list respectively) by `StandardNotation` —
declaration order in the source text doesn't matter. The resolved map is
exposed as `grammar.lexicalTokens`.

The Swift DSL (scenario F) doesn't need this indirection at all: write the
compiled terminal directly at its point of use with `rt(_:)`, `ct(_:)`, or
`lt(_:)`, e.g. `Rule("digit") { ct("0"..."9") }`.

## 5. Preparing the grammar for a parser

A freshly-imported `Grammar` is rarely what a specific parsing algorithm
wants directly. The relevant transformations, all `Grammar` methods:

| Call                                                                                 | Produces                                                  | Typically needed for                                                   |
| ------------------------------------------------------------------------------------ | --------------------------------------------------------- | ---------------------------------------------------------------------- |
| `grammar.rewriteToStandardForm()` → `([Production], Set<NonTerminal>)`               | Flattened EBNF-construct-free BNF                         | Nearly everything; also triggered by `grammar.grammarForm = .standard` |
| `Grammar.eliminateEmpty(productions:start:)` (static, `Hygiene.swift`)               | Removes ε-productions except possibly at the start symbol | LL/LR table construction                                               |
| `Grammar.eliminateUnitRules(productions:)` (static)                                  | Removes `A -> B` chain rules                              | LL/LR                                                                  |
| `Grammar.eliminateUnusedProductions(productions:start:)` (static)                    | Drops unreachable/non-generating rules                    | Cleanup before any table-based parser                                  |
| `grammar.eliminateLeftRecursion()` → `[Production]`                                  | Removes direct/indirect left recursion                    | LL(1) and other top-down parsers                                       |
| `grammar.leftFactoring()` → `[Production]`                                           | Factors out common alternative prefixes                   | LL(1)                                                                  |
| `grammar.firstAndFollow()` / `grammar.followSets()` / `grammar.isLL1(first:follow:)` | FIRST/FOLLOW sets, LL(1) check                            | LL table construction, conflict diagnostics                            |
| `grammar.toChomskyNormalForm()` → `Grammar`                                          | CNF (all rules `A -> BC` or `A -> a`)                     | CYK                                                                    |
| `grammar.toGreibachNormalForm()` → `Grammar`                                         | GNF (all rules start with a terminal)                     | Certain top-down/recursive-descent constructions                       |

## 6. Handing off to an actual parser

This repository's job ends at producing a (possibly normalized) `Grammar`.
The recognition step — turning a `Grammar` plus an input string into a parse
tree or SPPF — lives in one of the sibling packages (Earley-Parser,
Earley-TableParser, LL-Parsing, LR-Parsing, CYK-Parser, RNGLR-Parser, GLR),
each consuming a `Grammar` already rewritten into whatever form that
algorithm expects (CYK wants Chomsky Normal Form; LL wants left recursion and
common prefixes removed first; Earley/GLR/RNGLR generally work directly off
standard form). What every one of them has to work with, regardless of which
scenario in §3 produced it, is the same `[Production]` / `Symbol` / `Terminal`
/ `NonTerminal` shapes described in §2 — that consistency is the entire point
of funneling all seven scenarios through the same normalization layer.

## 7. Which scenario should I use?

- **Loading a grammar from a file/config at runtime, in a notation a human
  will hand-edit** → A/B/C/D (pick based on which punctuation style you or
  your grammar's original source already uses; D if you want the start
  symbol embedded in the text itself).
- **Building a grammar in Swift, and it has any `|`, `[ ]`, `{ }`, or `( )`**
  → F (the DSL) — you get synthetic non-terminal generation for free.
- **Building a grammar in Swift that's already a flat list of alternative-free
  rules** → E, or G if you'd rather use a trailing closure than an array
  literal.
- **You already have a `Grammar` and need it in a specific normal form for a
  specific parser** → §5, not a different construction scenario.
