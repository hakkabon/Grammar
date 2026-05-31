# Grammar Normal Forms: CNF and GNF

This document explains the two grammar normal form conversions implemented in the Grammar framework: **Chomsky Normal Form (CNF)** and **Greibach Normal Form (GNF)**. Both are transformations that rewrite any context-free grammar (CFG) into an equivalent grammar with a restricted production shape, without changing the language the grammar generates.

---

## Background: Why Normal Forms?

A context-free grammar `G = (V, T, P, S)` can have productions of arbitrary shape. Normal forms impose a uniform structure that:

- Simplifies proofs about CFGs (e.g. the pumping lemma for CFLs uses CNF)
- Enables specific parsing algorithms (CYK parsing requires CNF; certain top-down parsers benefit from GNF)
- Makes grammar analysis tractable by bounding the shape of each rule

Both conversions are **language-preserving**: the transformed grammar generates exactly the same set of strings as the original (with the possible exception of the empty string ε, which requires special handling).

---

## Chomsky Normal Form (CNF)

### Definition

A CFG is in **Chomsky Normal Form** if every production has one of these three shapes:

```
A → a          (a single terminal symbol)
A → B C        (exactly two non-terminal symbols)
S → ε          (only the start symbol may derive the empty string)
```

No other production shapes are allowed. In particular:
- Rules with three or more symbols are forbidden
- Unit productions `A → B` are forbidden
- Terminals mixed with non-terminals in the same rule are forbidden

### Why CNF?

CNF is the foundation of the **CYK (Cocke–Younger–Kasami) algorithm**, a bottom-up chart parser that runs in O(n³) time. CYK works by filling a triangular table where each cell `[i,j]` holds the set of non-terminals that can derive the substring from position `i` to `j`. The binary structure of CNF rules makes this table-filling straightforward.

CNF is also used in theoretical proofs. The pumping lemma for context-free languages, for example, is most cleanly stated using CNF parse trees, where every internal node has exactly two children.

### Conversion Algorithm

The conversion proceeds in four steps. Each step preserves the generated language.

#### Step 1 — Eliminate ε-productions

An ε-production is any rule `A → ε`. These are removed by:

1. Computing the **nullable set**: all non-terminals `A` such that `A ⇒* ε`. This is done with a fixed-point iteration:
   - Basis: any `A` with a direct `A → ε` rule is nullable.
   - Induction: if `A → α` and every symbol in `α` is nullable, then `A` is nullable.

2. For every production `A → α`, generate all combinations of `α` where nullable symbols are either present or absent. For example, if `B` is nullable:
   ```
   A → a B c    becomes    A → a B c  |  A → a c
   ```

3. Drop all original ε-productions (except `S → ε` if the original language contains ε).

#### Step 2 — Eliminate unit productions

A unit production is `A → B` where `B` is a single non-terminal. These are removed by:

1. Computing the **unit-reachability relation**: `A` can reach `B` if `A ⇒* B` via a chain of unit productions. This is the transitive closure of the unit-production relation.

2. For each pair `(A, B)` in the reachability relation, add all non-unit productions of `B` directly to `A`.

3. Remove all unit productions.

For example:
```
S → A,  A → B,  B → "b"
```
After unit elimination, both `S` and `A` directly produce `"b"`.

#### Step 3 — TERM: Replace terminals in long rules

After steps 1 and 2, some rules may still mix terminals and non-terminals, or have terminals in rules of length ≥ 2. For every terminal `a` appearing in a rule of length ≥ 2, introduce a fresh non-terminal `Ta` with the single production `Ta → a`, and replace `a` with `Ta` in the rule.

```
A → "a" B "c"    becomes    A → Ta B Tc
                             Ta → "a"
                             Tc → "c"
```

#### Step 4 — BIN: Binarise long rules

Any rule of length ≥ 3 is broken into a right-branching chain of binary rules using fresh non-terminals:

```
A → B C D E    becomes    A  → B Y0
                           Y0 → C Y1
                           Y1 → D E
```

This is the final step. After BIN, every rule has at most two symbols on the right-hand side.

### Implementation Notes

The converter is `Grammar.ChomskyNormalFormConverter`. It is accessed via the public method `Grammar.toChomskyNormalForm()` which returns a new `Grammar` value.

The converter uses a private instance counter to generate unique non-terminal names (`T0`, `T1`, … for terminal wrappers; `Y0`, `Y1`, … for binarisation helpers). The counter is reset at the start of each conversion.

The `Grammar.isInChomskyNormalForm` property can be used to verify the result.

---

## Greibach Normal Form (GNF)

### Definition

A CFG is in **Greibach Normal Form** if every production has the shape:

```
A → a α        (a single terminal followed by zero or more non-terminals)
```

where `a` is a terminal and `α ∈ V*` (a possibly empty sequence of non-terminals). No terminals may appear in `α`.

### Why GNF?

GNF is useful for **top-down parsing** and for proving properties of pushdown automata (PDAs). Every GNF grammar can be directly simulated by a PDA that reads exactly one input symbol per derivation step. This makes the relationship between CFGs and PDAs particularly clean.

GNF also guarantees that no left recursion exists in the grammar, which is a prerequisite for many LL parsing strategies.

### Conversion Algorithm

The conversion builds on the same preliminary steps as CNF, then adds grammar-specific transformations.

#### Steps 1 & 2 — Eliminate ε-productions and unit productions

These are identical to the CNF steps and are reused from `ChomskyNormalFormConverter`.

#### Step 3 — Order non-terminals and eliminate left recursion

This is the **Rosenkrantz–Stearns algorithm** (also described in Hopcroft, Motwani & Ullman). The non-terminals are given a total order `A1, A2, …, An` (alphabetical in this implementation).

For each `Ai` in order:

1. **Substitute lower-indexed non-terminals**: For every rule `Ai → Aj γ` where `j < i`, replace it with all rules `Aj → δ` substituted in: `Ai → δ γ`. This ensures that after processing `Ai`, no rule for `Ai` starts with `Aj` for any `j ≤ i`.

2. **Eliminate immediate left recursion**: After substitution, `Ai` may have rules of the form `Ai → Ai α` (immediate left recursion). These are eliminated using the standard transformation:
   ```
   Ai  → β Ai'    (for each non-recursive rule Ai → β)
   Ai' → α Ai'    (for each recursive suffix α)
   Ai' → ε        (base case)
   ```
   where `Ai'` is a fresh non-terminal.

After processing all `Ai` in order, no rule for any `Ai` starts with `Aj` where `j ≤ i`. The rules for `An` (the last non-terminal) already start with terminals.

#### Step 4 — Back-substitution

Working from `An` back down to `A1`, substitute the rules of higher-indexed non-terminals into lower-indexed ones until every rule starts with a terminal. This is done by `expandUntilTerminalFirst`, which recursively replaces a leading non-terminal with all its productions until a terminal is reached.

#### Step 5 — Wrap tail terminals

GNF requires that every symbol after the leading terminal is a non-terminal. Any terminal `a` appearing at position ≥ 1 in a rule is replaced with a fresh non-terminal `Ta → a`, exactly as in the CNF TERM step.

```
A → "a" B "c" D    becomes    A  → "a" B Tc D
                               Tc → "c"
```

### Implementation Notes

The converter is `Grammar.GreibachNormalFormConverter`. It is accessed via `Grammar.toGreibachNormalForm()`.

The converter reuses `ChomskyNormalFormConverter.eliminateEpsilonProductions` and `eliminateUnitProductions` (both are `internal` methods, accessible within the same module). Fresh non-terminals use the prefix `Z` for left-recursion elimination helpers (e.g. `A'` becomes `A'0`), and `T` for tail terminal wrappers.

The `Grammar.isInGreilbachForm` property verifies the result.

---

## Comparison

| Property | CNF | GNF |
|---|---|---|
| Rule shape | `A → a` or `A → B C` | `A → a α` (α ∈ V*) |
| Max rule length | 2 | Unbounded |
| Terminals in tail | Not applicable | Forbidden |
| Left recursion | Allowed | Eliminated |
| Primary use | CYK parsing, pumping lemma | Top-down parsing, PDA simulation |
| Preserves ε | Only via `S → ε` | No |

Both forms are **equivalent** in expressive power: any CFG can be converted to either form, and both generate the same language as the original grammar (modulo ε).

---

## Code Structure

```
Sources/Grammar/GrammarForms/
├── GrammarForms.swift       — isInChomskyNormalForm, isInGreilbachForm properties
├── ChomskyForm.swift        — ChomskyNormalFormConverter, Grammar.toChomskyNormalForm()
└── GreilbachForm.swift      — GreibachNormalFormConverter, Grammar.toGreibachNormalForm()

Tests/GrammarTests/
├── ChomskyFormTests.swift   — 14 tests covering all CNF conversion steps
└── GreilbachFormTests.swift — 12 tests covering all GNF conversion steps
```

The helper extensions `isTerminal`, `isNonTerminal`, `isEpsilon`, `nonTerminal`, and `terminal` on `Symbol` are defined in `Sources/Grammar/Symbols/Symbol.swift` and are used throughout both converters.
