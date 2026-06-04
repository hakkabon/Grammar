# Grammar Package — Comprehensive Implementation Guide

This document gives an in-depth explanation of every subsystem in the Grammar Swift package.

---

## 1. The Symbol Type Hierarchy

Everything in a grammar rule is a `Symbol`. Three mutually exclusive kinds exist:

```
Symbol
├── .terminal(Terminal)
├── .nonTerminal(NonTerminal)
└── .metaSymbol(MetaSymbol)
```

### Terminal

A `Terminal` represents an atomic piece of input that the parser matches literally against the input stream. Four variants:

| Variant | Example | Notes |
|---|---|---|
| `.string(String)` | `"+"`, `"if"` | Exact string match |
| `.characterRange(ClosedRange<Character>)` | `"a"..."z"` | Single character in range |
| `.regularExpression(NSRegularExpression)` | `[0-9]+` | Matched with `NSRegularExpression` |
| `.meta(MetaTerminal)` | `ε`, `$` | Boundary markers (see below) |

Terminal equality is semantically interesting: a `.regularExpression` compared against a `.string` performs actual regex matching, so `Terminal.regularExpression("[a-z]+") == Terminal.string("abc")` is `true`.

Convenience: `Terminal` conforms to `ExpressibleByStringLiteral`, so `let t: Terminal = "+"` works.

### MetaTerminal

Boundary markers that survive into the final grammar (unlike `MetaSymbol`s, which are eliminated):

| Case | Raw value | Meaning |
|---|---|---|
| `.eps` | `ε` | Empty string (epsilon) |
| `.lambda` | `λ` | Alternate epsilon notation |
| `.eof` | `$` | End of input stream |
| `.eop` | `¶` | End of production |
| `.empty` | `""` | Invisible empty (displayed as `''`) |

`Terminal.isEmpty` returns `true` for `.string("")`, `.meta(.eps)`, `.meta(.lambda)`, and `.meta(.empty)`. This property drives nullable detection.

### MetaSymbol

Structural EBNF notation characters that appear in raw parsed productions but must be fully eliminated before any parsing algorithm runs:

```
{ } [ ] ( ) |
```

These are removed by `StandardForm.rewriteToStandardForm()` and `StandardNotation.rewriteToStandardNotation(syntax:)`.

### NonTerminal

A `NonTerminal` is a named placeholder for a set of strings. It is a simple `struct` wrapping a `String name`. It is `Equatable`, `Hashable`, `Comparable` (alphabetically), and `ExpressibleByStringLiteral`:

```swift
let S: NonTerminal = "S"
```

### Symbol helper extensions

`Symbol` exposes several computed properties added in this codebase:

| Property | Description |
|---|---|
| `isTerminal` | `true` if `.terminal(_)` |
| `isNonTerminal` | `true` if `.nonTerminal(_)` |
| `isEpsilon` | `true` if the symbol represents the empty string |
| `nonTerminal: NonTerminal?` | Unwraps `.nonTerminal` case |
| `terminal: Terminal?` | Unwraps `.terminal` case |

`[Symbol]` has `isNullable` (all members are empty), `hasPrefix(_:)`, and `commonPrefix(with:)`.

### Factory functions

`Symbols.swift` provides short-hand helpers used throughout the codebase and in tests:

```swift
t("a")          // .terminal(.string("a"))
n("E")          // .nonTerminal(NonTerminal(name: "E"))
rt("[0-9]+")    // .terminal(.regularExpression(...))   throws
mt("ε")         // .terminal(.meta(.eps))
ms("{")         // .metaSymbol(.lbrace)
```

---

## 2. Grammar and Production

### Production

`Production` is an immutable value type:

```swift
struct Production {
    let goal: NonTerminal   // LHS
    let rule: [Symbol]      // RHS
}
```

Computed properties relevant to parsing:

| Property | Description |
|---|---|
| `isFinal` | All symbols in `rule` are terminals |
| `isInChomskyNormalForm` | Rule is `A → a` or `A → B C` |
| `isNullable` | Rule is empty or contains only epsilon terminals |
| `generatedTerminals` | Terminals in `rule`, in order |
| `generatedNonTerminals` | Non-terminals in `rule`, in order |
| `containsSymbol(_:)` | Returns `(match, position)` if symbol is found |

`Production` is `Hashable`, `Equatable`, `Comparable` (by goal then rule length), `Codable`.

### Grammar

`Grammar` is the top-level value type. Its core stored properties:

```swift
var productions: [Production]
var start: NonTerminal
var epsilon: MetaTerminal        // default .eps
var endofile: MetaTerminal       // default .eof
var generatedNonTerminals: Set<NonTerminal>
let lexicalTokens: [String: String]
var syntaxTree: BnfExpression
let nullableNonTerminals: Set<NonTerminal>   // computed at init
```

**Nullable computation at init time**: The initialiser immediately runs a two-phase fixed-point algorithm to compute `nullableNonTerminals`:
1. Seed with every non-terminal that has a direct `A → ε` production.
2. Iteratively add any `A → α` where every symbol in `α` is already nullable.

This set is used throughout analysis (FIRST/FOLLOW, CNF, GNF).

**Computed properties**:
- `nonTerminals` — union of all goal symbols and all non-terminals appearing on the RHS
- `terminals` — all terminals appearing in any rule
- `startProduction` — the first production whose goal equals `start`

**String output** (`bnf`, `ebnf`, `wsn`): Productions are grouped by goal (alphabetically), alternatives are joined with `|`, and the appropriate notation markers are applied.

**`GrammarForm`** property observer: setting `grammarForm = .standard` triggers `rewriteToStandardForm()` in-place.

---

## 3. Grammar Import (Parsing from Text)

All three textual parsers share the same pipeline:

```
String input
    │
    ▼
GrammarParser (tokenizer-driven recursive descent)
    │
    ▼
BnfExpression  (AST)
    │
    ▼
StandardNotation.rewriteToStandardNotation(syntax:)
    │
    ▼
[Production] + Set<NonTerminal>  (flat BNF)
    │
    ▼
Grammar initialiser
```

### GrammarParser

A hand-written recursive-descent parser backed by a `Tokenizer` (from the `GrammarTokenizer` dependency). Key capabilities:

- Accepts BNF (`<name> ::= …`) and EBNF/WSN (`name = …`) notation in the same file.
- Parses EBNF structural constructs: `{ }` (repetition), `[ ]` (option), `( )` (grouping).
- Parses `lexical { }` blocks for type-3 (regex / range / list) definitions.
- Collects parser diagnostics (`ParserDiagnostic`) and reports them with source locations and coloured squiggles.
- Performs **panic-mode error recovery**: after a syntax error, it advances tokens until it finds the start of the next production.

The grammar for the parser's input language (a superset of WSN) is documented in the file-level comment of `GrammarParser.swift`.

### BnfExpression

An `indirect enum` AST node type. Covers every construct the parser recognises:

```swift
public indirect enum BnfExpression {
    case syntax([BnfExpression])
    case production(String, BnfExpression)
    case sequence([BnfExpression])
    case alternative([BnfExpression])
    case optional(BnfExpression)
    case repetition(BnfExpression)
    case repetitionOnePlus(BnfExpression)
    case grouping(BnfExpression)
    case terminal(String)
    case nonterminal(String)
    case range(String, String, String)
    case list(String, [String])
    case regex(String, String)
    case emptyStringSymbol(String)
    case endOfFileSymbol(String)
    case startSymbol(String)
}
```

`BnfExpression` conforms to `Equatable`, `Hashable`, `Codable`, and `CustomStringConvertible` (the latter renders a coloured tree via `TreePrinter`).

### StandardNotation

`StandardNotation.rewriteToStandardNotation(syntax:)` flattens the `BnfExpression` AST into a `[Production]` list:

- `.terminal` → `[.terminal(.string(value))]` or `[.terminal(.meta(…))]`
- `.nonterminal` → `[.nonTerminal(NonTerminal(name:))]`
- `.alternative` → introduces a fresh `@alt_N` non-terminal with one production per branch
- `.optional` → introduces `@opt_N → content | ε`
- `.repetition` → introduces `@rep_N → content @rep_N | ε` (right-recursive)
- `.repetitionOnePlus` → introduces `@rep1_N → content | content @rep1_N`
- `.grouping` → inlined as a sequence (no new non-terminal unless it contains an alternative)

Fresh non-terminal names are generated via `Counter.next()` with an `@prefix_N` pattern to avoid collisions.

---

## 4. Standard Form Rewriting

`StandardForm.swift` handles a different but related task: productions that were read from the symbol stream and still contain raw `MetaSymbol` tokens (`{`, `[`, `(`, `|`). This happens when a grammar is constructed programmatically using the older operator DSL.

The algorithm walks each production's `rule: [Symbol]` array, finds matching bracket pairs using a `Stack`, and applies one of three rewrites:

| MetaSymbol pair | Rewrite |
|---|---|
| `( … )` grouping | `A → α(X₁…Xₙ)β` becomes `A → αNβ`, `N → X₁…Xₙ` |
| `[ … ]` option | `A → α[X₁…Xₙ]β` becomes `A → αNβ`, `N → X₁…Xₙ`, `N → ε` |
| `{ … }` repetition | `A → γ{X₁…Xₘ}δ` becomes `A → γNδ`, `N → X₁…XₘN`, `N → ε` |

After bracket-pair reduction, `rewriteAlternations` splits any remaining `| MetaSymbol` positions into separate productions.

The worklist-based loop ensures nested constructs are handled correctly: each rewrite may produce new productions that themselves contain meta-symbols, and these are pushed back onto the worklist.

---

## 5. Grammar Builder DSL

Two independent DSLs exist for writing grammars directly in Swift.

### Operator DSL (`ProductionResult`)

Based on custom infix operators. Precedence: `<+>` (concatenation) > `<|>` (alternation) > `-->` (production):

```swift
"S" --> n("A") <+> n("B")                     // S → A B
"S" --> t("a") <|> t("b")                     // S → a | b
"S" --> n("A") <+> n("B") <|> t("c")         // S → A B | c
```

`ProductionResult` is either `.con([Symbol])` (concatenation) or `.alt([[Symbol]])` (alternatives). The `-->` operator unpacks it into one or more `Production` values.

### Result-builder DSL (`RuleBuilder`, `GrammarBuilders`)

A higher-level DSL inspired by SwiftUI:

```swift
Grammar(start: "E") {
    Rule("E") {
        Alt {
            Cat { n("E") ; t("+") ; n("T") }
            n("T")
        }
    }
    Rule("T") { t("n") }
}
```

The building blocks:

| Type | Builder | Meaning |
|---|---|---|
| `Rule("name") { … }` | `@RuleCatBuilder` | Production; implicit operator is concatenation |
| `Cat { … }` | `@RuleCatBuilder` | Explicit concatenation group |
| `Alt { … }` | `@RuleAltBuilder` | Alternatives; implicit operator is alternation |
| `Seq { … }` | `@RuleCatBuilder` | Zero-or-more repetition `{ }` |
| `Grp { … }` | `@RuleCatBuilder` | Grouping `( )` |
| `Opt { … }` | `@RuleCatBuilder` | Option `[ ]` |

All of these produce `Rule.Expression` values. The `@GrammarBuilder` at the `Grammar(start:)` level assembles a `[Production]` array from the `Rule` values.

---

## 6. Grammar Analysis

### FIRST and FOLLOW Sets (`FirstFollow.swift`)

**FIRST(α)** is the set of terminals that can begin strings derived from α. **FOLLOW(A)** is the set of terminals that can immediately follow A in any sentential form.

Both are computed via fixed-point iteration:

1. Initialise `FIRST[t] = {t}` for each terminal; `FIRST[A] = ∅` for each non-terminal.
2. For each `A → X₁ X₂ … Xₙ`: add `FIRST(X₁) − {ε}`, and if X₁ is nullable add `FIRST(X₂) − {ε}`, etc. Repeat until stable.
3. Initialise `FOLLOW[S] = {$}`.
4. For each `A → αBβ`: add `FIRST(β) − {ε}` to `FOLLOW(B)`. If β is nullable add `FOLLOW(A)` to `FOLLOW(B)`. Repeat until stable.

The main entry point `firstAndFollow()` computes both in one call and returns `([Symbol: Set<Symbol>], [NonTerminal: Set<Symbol>])`.

`isLL1(first:follow:)` checks the LL(1) condition: for every non-terminal, its productions must have pairwise disjoint PREDICT sets.

### Nullable Computation (`Nullable.swift`)

`allNullableNonTerminals()` re-computes the nullable set on demand (the stored `nullableNonTerminals` is computed at init time). `isNullable(_:)` checks either a single non-terminal or a sequence of symbols.

### Left Factoring (`LeftFactoring.swift`)

Implements Dragon Book Algorithm 4.21. For each non-terminal A:

1. Find the longest common prefix α of all A-productions.
2. While |α| > 0:
   - Create a fresh non-terminal V.
   - Replace all A → αβᵢ with A → αV and V → βᵢ.
   - Recompute the longest common prefix.

### Left-Recursion Elimination (`LeftRecursion.swift`)

Implements Dragon Book Algorithm 4.19. Handles both direct and indirect left recursion.

For direct recursion `A → Aα | β`:
- Replace with `A → βA'`, `A' → αA' | ε`.

For indirect recursion, the algorithm orders non-terminals A₁…Aₙ and for each Aᵢ substitutes all Aᵢ → Aⱼγ where j < i, then eliminates any resulting direct left recursion.

### Cycle Detection (`CycleDetection.swift`)

Uses depth-first search with a three-colour marking scheme (unvisited / in-stack / done). A back edge in the DFS tree indicates a cycle. All cycles are collected as paths of `Symbol` values.

### Grammar Hygiene (`Hygiene.swift`)

Three classical grammar cleaning operations:

**`eliminateUnusedProductions`**: DFS from the start symbol; discards any production whose goal is not reachable.

**`eliminateUnitRules`**: Replaces every chain `A → B → … → C → α` (where each step is a unit production) with the direct rule `A → α`, recording the chain for traceability.

**`eliminateEmpty`**: Removes ε-productions by expanding every occurrence of a nullable non-terminal. Preserves the empty production for the start symbol only.

---

## 7. Normal Form Conversions

### Chomsky Normal Form (`ChomskyForm.swift`)

**Goal**: Every production is `A → a` or `A → B C`.

Four sequential steps, each operating on a `[NonTerminal: [[Symbol]]]` grouped representation:

**Step 1 — ε-elimination**: Compute the nullable set. For each rule, generate all combinations where nullable symbols are optionally removed. Drop the original ε-productions.

**Step 2 — Unit production elimination**: Compute the transitive closure of the unit-reachability relation (`A ⇒* B` via unit steps). Replace each `A → B` with all non-unit productions of B.

**Step 3 — TERM**: For every rule of length ≥ 2, replace each terminal `a` with a fresh non-terminal `Tₙ → a`. This ensures that in binary rules, both positions hold non-terminals.

**Step 4 — BIN**: Break every rule of length ≥ 3 into a right-branching chain of binary rules:
```
A → B C D E  ⟹  A → B Y₀
                 Y₀ → C Y₁
                 Y₁ → D E
```

Public API: `Grammar.toChomskyNormalForm() -> Grammar`.

### Greibach Normal Form (`GreilbachForm.swift`)

**Goal**: Every production is `A → a α` where `a` is a terminal and `α ∈ V*`.

Six sequential steps:

**Steps 1–2** — same ε and unit elimination as CNF.

**Step 3 — Order and substitute**: Sort non-terminals alphabetically as A₁…Aₙ. For each Aᵢ, replace any rule `Aᵢ → Aⱼ γ` (j < i) by substituting all Aⱼ-productions. This enforces the ordering invariant.

**Step 4 — Immediate left-recursion elimination**: For each Aᵢ that has rules of the form `Aᵢ → Aᵢ α | β`, introduce `Aᵢ'` and rewrite to `Aᵢ → β Aᵢ'` and `Aᵢ' → α Aᵢ' | ε`.

**Step 5 — Back-substitution**: Working from Aₙ down to A₁, expand any leading non-terminal until every rule starts with a terminal.

**Step 6 — Tail-terminal wrapping**: GNF forbids terminals after position 0. Any terminal `a` at position ≥ 1 is replaced with a fresh `Tₙ → a`.

Public API: `Grammar.toGreibachNormalForm() -> Grammar`.

---

## 8. Grammar Pretty Printer and Documentation Generator

### GrammarPrettyPrinter

Walks a `BnfExpression` tree and re-serialises it to a formatted string. Uses a `Precedence` enum to determine when to insert parentheses automatically:

```
lowest < alternative < sequence < suffix < atom
```

An `.alternative` inside a `.sequence` context gets wrapped in `( … )` because `alternative < sequence`. An `.alternative` at the lowest context level does not get wrapped.

Configuration: `definitionOperator` (`::=` or `=`), `terminator` (`;` or `.`), `indentWidth`.

### GrammarDocumenter

Combines `GrammarPrettyPrinter` and `GrammarToRailroad` to produce a side-by-side formatted source + ASCII diagram for each production in a grammar.

### GrammarToRailroad

Converts `BnfExpression` nodes recursively to `DiagramElement` values from the `GrammarDiagram` package, then renders them to ASCII art:

| BnfExpression | DiagramElement |
|---|---|
| `.terminal` | `terminal(name)` |
| `.nonterminal` | `nonTerminal(name)` |
| `.sequence` | `sequence([…])` |
| `.alternative` | `choice([…])` |
| `.optional` | `optional(…)` |
| `.repetition` | `optional(repeater(…))` |
| `.repetitionOnePlus` | `group(sequence([…, choice([…])]))` |
| `.emptyStringSymbol` | `skip()` |

---

## 9. ADTs

### Stack<T>

Value-type LIFO backed by an `Array`. Conforms to `ExpressibleByArrayLiteral`. Operations: `push`, `pop`, `top`, `isEmpty`, `count`. Used by `StandardForm.matchingSymbols` to track bracket nesting.

### Queue<T>

Reference-type FIFO backed by an `Array` with an advancing `head` index. Performs a compacting `removeFirst(head)` sweep when the queue exceeds 50 elements and more than half have been consumed. Operations: `enqueue`, `dequeue`, `front`, `isEmpty`, `count`.

### List<T> / MutableList<T>

Reference-type random-access collection wrapping an `Array<T>`. Adds functional operations (`appending`, `filter`, `map`, `compactMap`, `flatMap`, `sorted`) that return new `List<T>` values. `MutableList<T>` adds mutating operations (`append`, `insert`, `remove`, `removeFirst`, `removeLast`, `reverse`).

---

## 10. Extensions

### String+Extensions

Extensive regex API: `matches(_:)` (whole-string match), `matches(for:)`, `hasRegularPrefix`, `rangeOfRegularPrefix`, `hasRegularSuffix`, `rangeOfRegularSuffix`. These wrap `NSRegularExpression` and are used internally by `Terminal.==` and the parser.

Terminal-based prefix matching: `hasPrefix(_:Terminal, from:)` and `rangeOfPrefix(_:from:)` dispatch on the `Terminal` case to perform string, range, or regex prefix checks.

String escaping: `literalEscaped`, `singleQuoteLiteralEscaped`, `doubleQuoteLiteralEscaped` — used when serialising grammars back to text.

### Sequence+Extensions

| API | Description |
|---|---|
| `unique(by:)` | Lazily deduplicate by a key function |
| `strided(_:start:)` | Lazy stride iteration |
| `pairs()` | Consecutive pairs (sliding window of 2) |
| `prefixes()` | Increasing prefixes `[a]`, `[a,b]`, `[a,b,c]`, … |
| `combinations()` | Cartesian product of nested sequences |
| `partition(_:)` | Split into two arrays by predicate |
| `collect(_:)` | Pipe to a collector: `seq.filter{…}.collect(Set.init)` |

### Collection+Extensions

`longestCommonPrefix()` and `longestCommonSuffix()` on `Collection where Element: StringProtocol`. Used by `leftFactoring()`.

---

## 11. Utils

### Counter

Thread-safe (Swift static properties are atomic) monotonic integer. `Counter.next()` increments and returns. `Counter.reset()` resets to zero. Used by `StandardNotation` when naming synthetic non-terminals.

### Either<A,B>

Standard generic sum type. `map(_:_:)` transforms both branches independently; `combine(_:_:)` folds both branches into the same result type.

### mod(_:with:)

Mathematically correct modulus:
- `mod(-7, with: 3)` → 2  (not -1 as Swift's `%` returns)
- Handles negative `b` by negating both arguments

### Sequence utilities (Sequence.swift)

| API | Description |
|---|---|
| `product(_:)` / `*` operator | Cartesian product of two sequences |
| `crossProduct(_:_:)` | Lazy cartesian product |
| `crossMap(_:_:transform:)` | Map over cartesian product |
| `crossFlatMap(_:_:transform:)` | FlatMap over cartesian product |
| `unzip(_:)` | Split a sequence of pairs into two sequences |

The `ProductionResult.<+>` operator uses `*` to expand alternation concatenation.

---

## 12. GrammarFuzzer

`GrammarFuzzer` (base) and `SimpleGrammarFuzzer` generate strings that belong to the grammar's language by repeatedly expanding non-terminals.

`DerivationNode` is a tree node representing one step in the derivation. A leaf holds a terminal; an internal node holds a non-terminal and its expanded children. The tree records the full derivation history, allowing test engineers to inspect which productions were applied.

`SimpleGrammarFuzzer` picks a random alternative for each non-terminal. A budget parameter limits the total derivation depth to avoid infinite expansion for recursive grammars.

---

## 13. Logging

`GrammarLogger.swift` defines two OSLog categories:

| Logger | Category | Used for |
|---|---|---|
| `Logger.grammar` | `"Grammar"` | Standard form rewriting, left factoring |
| `Logger.bnf` | `"BNF-parser"` | Grammar parser lookahead traces |

Both use the subsystem `"com.grammar.hakkabon"` and are inactive unless an attached system logger is filtering at `trace` level.
