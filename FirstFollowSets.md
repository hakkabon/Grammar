# FIRST and FOLLOW Sets

This document provides an in-depth explanation of FIRST and FOLLOW set computation for context-free grammars (CFGs). These sets are fundamental to constructing predictive parsers and determining whether a grammar is LL(1).

---

## Table of Contents

1. [Introduction](#introduction)
2. [FIRST Sets](#first-sets)
3. [FOLLOW Sets](#follow-sets)
4. [Implementation Details](#implementation-details)
5. [Examples](#examples)
6. [LL(1) Grammars](#ll1-grammars)

---

## Introduction

### What are FIRST and FOLLOW Sets?

**FIRST sets** and **FOLLOW sets** are used in top-down parsing to determine which production to apply when multiple alternatives exist. They answer two key questions:

- **FIRST(α)**: What terminals can appear at the beginning of strings derived from α?
- **FOLLOW(A)**: What terminals can appear immediately after non-terminal A in any sentential form?

### Why are they important?

These sets are essential for:
- **Constructing LL(1) parsers**: Predictive parsers that make parsing decisions without backtracking
- **Building parse tables**: Mapping (non-terminal, terminal) pairs to productions
- **Grammar analysis**: Determining if a grammar is suitable for top-down parsing
- **Error detection**: Identifying ambiguities and conflicts in grammar rules

---

## FIRST Sets

### Definition

For a string of grammar symbols α (terminals and non-terminals), **FIRST(α)** is the set of terminals that can appear as the first symbol of some string derived from α.

Formally:
```
FIRST(α) = { a ∈ T | α ⇒* aβ for some β }
```

If α can derive the empty string (ε), then ε ∈ FIRST(α).

### Computation Algorithm

The FIRST set is computed using a fixed-point iteration:

#### Base Cases:

1. **For a terminal `a`**:
   ```
   FIRST(a) = { a }
   ```

2. **For epsilon (ε)**:
   ```
   FIRST(ε) = { ε }
   ```

3. **For a non-terminal `A` with production `A → ε`**:
   ```
   ε ∈ FIRST(A)
   ```

#### Recursive Cases:

4. **For a non-terminal `A` with production `A → X₁ X₂ ... Xₙ`**:
   
   a. Add FIRST(X₁) - {ε} to FIRST(A)
   
   b. If ε ∈ FIRST(X₁), add FIRST(X₂) - {ε} to FIRST(A)
   
   c. Continue for X₃, X₄, ... as long as all previous symbols are nullable
   
   d. If all X₁, X₂, ..., Xₙ are nullable, add ε to FIRST(A)

#### Algorithm Pseudocode:

```
function computeFirstSets(grammar):
    // Initialize
    for each terminal t:
        FIRST[t] = {t}
    for each non-terminal A:
        FIRST[A] = ∅
    
    // Fixed-point iteration
    repeat:
        changed = false
        for each production A → X₁ X₂ ... Xₙ:
            // Add FIRST(X₁) - {ε}
            if FIRST[X₁] - {ε} ⊄ FIRST[A]:
                FIRST[A] = FIRST[A] ∪ (FIRST[X₁] - {ε})
                changed = true
            
            // If X₁ is nullable, continue to X₂
            k = 1
            while k ≤ n and ε ∈ FIRST[Xₖ]:
                if k < n:
                    if FIRST[Xₖ₊₁] - {ε} ⊄ FIRST[A]:
                        FIRST[A] = FIRST[A] ∪ (FIRST[Xₖ₊₁] - {ε})
                        changed = true
                k = k + 1
            
            // If all symbols are nullable
            if k > n and ε ∉ FIRST[A]:
                FIRST[A] = FIRST[A] ∪ {ε}
                changed = true
    until not changed
    
    return FIRST
```

### FIRST of a Sequence

For a sequence of symbols α = X₁ X₂ ... Xₙ:

```
FIRST(X₁ X₂ ... Xₙ) = FIRST(X₁)                           if ε ∉ FIRST(X₁)
                     = (FIRST(X₁) - {ε}) ∪ FIRST(X₂ ... Xₙ)  if ε ∈ FIRST(X₁)
```

In other words:
- Start with FIRST(X₁)
- If X₁ is nullable, add FIRST(X₂)
- Continue until you hit a non-nullable symbol or reach the end
- If all symbols are nullable, include ε in the result

### Examples

#### Example 1: Simple Grammar

```
S → A B
A → "a" | ε
B → "b"
```

**Computation:**
- FIRST(A) = {"a", ε}
- FIRST(B) = {"b"}
- FIRST(S) = FIRST(A B)
  - Add FIRST(A) - {ε} = {"a"}
  - Since ε ∈ FIRST(A), add FIRST(B) = {"b"}
  - Result: FIRST(S) = {"a", "b"}

#### Example 2: Chain of Nullables

```
S → A B C
A → ε
B → ε
C → "c"
```

**Computation:**
- FIRST(A) = {ε}
- FIRST(B) = {ε}
- FIRST(C) = {"c"}
- FIRST(S) = FIRST(A B C)
  - FIRST(A) - {ε} = ∅
  - A is nullable, so add FIRST(B) - {ε} = ∅
  - B is nullable, so add FIRST(C) = {"c"}
  - Result: FIRST(S) = {"c"}

#### Example 3: All Nullable

```
S → A B
A → ε
B → ε
```

**Computation:**
- FIRST(A) = {ε}
- FIRST(B) = {ε}
- FIRST(S) = FIRST(A B)
  - FIRST(A) - {ε} = ∅
  - A is nullable, so add FIRST(B) - {ε} = ∅
  - Both A and B are nullable, so add ε
  - Result: FIRST(S) = {ε}

---

## FOLLOW Sets

### Definition

For a non-terminal A, **FOLLOW(A)** is the set of terminals that can appear immediately to the right of A in some sentential form.

Formally:
```
FOLLOW(A) = { a ∈ T | S ⇒* αAaβ for some α, β }
```

If A can appear at the end of a derivation, then $ (end-of-input) ∈ FOLLOW(A).

### Computation Algorithm

The FOLLOW set is computed using a fixed-point iteration with these rules:

#### Rules:

1. **Start Symbol**:
   ```
   $ ∈ FOLLOW(S)
   ```
   where S is the start symbol and $ represents end-of-input.

2. **For production `A → α B β`**:
   
   a. Add FIRST(β) - {ε} to FOLLOW(B)
   
   b. If β is nullable (or empty), add FOLLOW(A) to FOLLOW(B)

#### Algorithm Pseudocode:

```
function computeFollowSets(grammar, firstSets):
    // Initialize
    for each non-terminal A:
        FOLLOW[A] = ∅
    FOLLOW[S] = {$}  // S is the start symbol
    
    // Fixed-point iteration
    repeat:
        changed = false
        for each production A → X₁ X₂ ... Xₙ:
            for i = 1 to n:
                if Xᵢ is a non-terminal B:
                    // β is everything after B
                    β = Xᵢ₊₁ Xᵢ₊₂ ... Xₙ
                    
                    // Add FIRST(β) - {ε} to FOLLOW(B)
                    if FIRST(β) - {ε} ⊄ FOLLOW[B]:
                        FOLLOW[B] = FOLLOW[B] ∪ (FIRST(β) - {ε})
                        changed = true
                    
                    // If β is nullable, add FOLLOW(A) to FOLLOW(B)
                    if ε ∈ FIRST(β):
                        if FOLLOW[A] ⊄ FOLLOW[B]:
                            FOLLOW[B] = FOLLOW[B] ∪ FOLLOW[A]
                            changed = true
    until not changed
    
    return FOLLOW
```

### Key Insights

1. **FOLLOW sets never contain ε**: They only contain terminals and $.

2. **Propagation**: FOLLOW sets can propagate through the grammar. If `A → αB` and B is at the end, then FOLLOW(A) ⊆ FOLLOW(B).

3. **Nullable symbols**: When computing FOLLOW(B) in `A → αBβ`, if β is nullable, we must include FOLLOW(A) in FOLLOW(B).

### Examples

#### Example 1: Terminal After

```
S → A "b"
A → "a"
```

**Computation:**
- FOLLOW(S) = {$}
- For production S → A "b":
  - β = "b"
  - FIRST(β) = {"b"}
  - Add {"b"} to FOLLOW(A)
- Result: FOLLOW(A) = {"b"}

#### Example 2: Non-Terminal After

```
S → A B
A → "a"
B → "b"
```

**Computation:**
- FOLLOW(S) = {$}
- For production S → A B:
  - β = B
  - FIRST(B) = {"b"}
  - Add {"b"} to FOLLOW(A)
  - B is at the end, so add FOLLOW(S) = {$} to FOLLOW(B)
- Result: FOLLOW(A) = {"b"}, FOLLOW(B) = {$}

#### Example 3: Nullable After

```
S → A B C
A → "a"
B → ε
C → "c"
```

**Computation:**
- FOLLOW(S) = {$}
- For production S → A B C:
  - After A: β = B C
    - FIRST(B C) = FIRST(B) - {ε} ∪ FIRST(C) = {"c"}
    - Add {"c"} to FOLLOW(A)
  - After B: β = C
    - FIRST(C) = {"c"}
    - Add {"c"} to FOLLOW(B)
  - After C: β = ε
    - Add FOLLOW(S) = {$} to FOLLOW(C)
- Result: FOLLOW(A) = {"c"}, FOLLOW(B) = {"c"}, FOLLOW(C) = {$}

#### Example 4: Propagation

```
S → A
A → "a"
```

**Computation:**
- FOLLOW(S) = {$}
- For production S → A:
  - A is at the end
  - Add FOLLOW(S) = {$} to FOLLOW(A)
- Result: FOLLOW(A) = {$}

---

## Implementation Details

### Data Structures

The implementation uses Swift dictionaries to store FIRST and FOLLOW sets:

```swift
var firstSets: [Symbol: Set<Symbol>] = [:]
var followSets: [NonTerminal: Set<Symbol>] = [:]
```

### Key Functions

#### 1. `firstAndFollow() -> ([Symbol: Set<Symbol>], [NonTerminal: Set<Symbol>])`

The main entry point that computes both FIRST and FOLLOW sets for the entire grammar.

**Algorithm:**
1. Initialize FIRST sets for all terminals and non-terminals
2. Iterate until fixed point for FIRST sets
3. Initialize FOLLOW sets with start symbol containing $
4. Iterate until fixed point for FOLLOW sets
5. Return both sets

#### 2. `computeFirst(of: [Symbol], using: [Symbol: Set<Symbol>]) -> Set<Symbol>`

Computes the FIRST set of a sequence of symbols using pre-computed FIRST sets.

**Parameters:**
- `of`: The sequence of symbols
- `using`: Pre-computed FIRST sets

**Returns:** The FIRST set of the sequence

#### 3. `first(of: [Symbol], using: [Symbol: Set<Symbol>]) -> (terminals: Set<Symbol>, nullable: Bool)`

Computes the FIRST set of a sequence and whether it's nullable.

**Returns:** A tuple containing:
- `terminals`: The FIRST set (excluding ε)
- `nullable`: Whether the entire sequence can derive ε

#### 4. `followSets() -> [NonTerminal: Set<Symbol>]`

Standalone function to compute FOLLOW sets. Internally calls `firstAndFollow()` to get FIRST sets first.

### Optimization Techniques

1. **Fixed-Point Iteration**: Both algorithms use fixed-point iteration, which continues until no changes occur. This ensures correctness even for complex grammars with cycles.

2. **Change Tracking**: The implementation tracks whether any set changed in each iteration to avoid unnecessary work.

3. **Pre-computation**: FOLLOW set computation pre-computes FIRST sets once rather than recomputing them for each production.

4. **Set Operations**: Uses Swift's efficient Set operations (union, subtraction, contains) for fast computation.

### Complexity

- **Time Complexity**: O(n³) in the worst case, where n is the size of the grammar
  - Each iteration examines all productions
  - Each production may update multiple sets
  - The number of iterations is bounded by the number of distinct symbols

- **Space Complexity**: O(n²) for storing FIRST and FOLLOW sets
  - Each non-terminal has a FIRST set
  - Each non-terminal has a FOLLOW set
  - Each set can contain up to O(n) terminals

---

## Examples

### Example 1: Simple Expression Grammar

```
E → T E'
E' → "+" T E' | ε
T → F T'
T' → "*" F T' | ε
F → "(" E ")" | "id"
```

**FIRST Sets:**
- FIRST(E) = {"(", "id"}
- FIRST(E') = {"+", ε}
- FIRST(T) = {"(", "id"}
- FIRST(T') = {"*", ε}
- FIRST(F) = {"(", "id"}

**FOLLOW Sets:**
- FOLLOW(E) = {$, ")"}
- FOLLOW(E') = {$, ")"}
- FOLLOW(T) = {$, ")", "+"}
- FOLLOW(T') = {$, ")", "+"}
- FOLLOW(F) = {$, ")", "+", "*"}

### Example 2: Balanced Parentheses

```
S → "(" S ")" S | ε
```

**FIRST Sets:**
- FIRST(S) = {"(", ε}

**FOLLOW Sets:**
- FOLLOW(S) = {$, ")"}

**Explanation:**
- S can start with "(" or be empty (ε)
- S can be followed by $ (end of input) or ")" (from the recursive structure)

### Example 3: If-Then-Else (Ambiguous)

```
S → "if" E "then" S
S → "if" E "then" S "else" S
S → "other"
E → "expr"
```

**FIRST Sets:**
- FIRST(S) = {"if", "other"}
- FIRST(E) = {"expr"}

**FOLLOW Sets:**
- FOLLOW(S) = {$, "else"}
- FOLLOW(E) = {"then"}

**Note:** This grammar is NOT LL(1) because both productions for S start with "if", creating a conflict.

---

## LL(1) Grammars

### Definition

A grammar is **LL(1)** if for every non-terminal A with productions:
```
A → α₁ | α₂ | ... | αₙ
```

The following conditions hold:

1. **Disjoint FIRST sets**: For all i ≠ j:
   ```
   FIRST(αᵢ) ∩ FIRST(αⱼ) = ∅
   ```

2. **No FIRST/FOLLOW conflict**: If ε ∈ FIRST(αᵢ), then:
   ```
   FIRST(αⱼ) ∩ FOLLOW(A) = ∅  for all j ≠ i
   ```

### Checking LL(1)

The `isLL1(first:follow:)` function checks if a grammar is LL(1):

```swift
public func isLL1(first: [Symbol:Set<Symbol>], follow: [NonTerminal:Set<Symbol>]) -> Bool
```

**Algorithm:**
1. For each non-terminal A, compute the **predict set** for each production
2. The predict set for `A → α` is:
   ```
   PREDICT(A → α) = FIRST(α)                    if ε ∉ FIRST(α)
                  = (FIRST(α) - {ε}) ∪ FOLLOW(A)  if ε ∈ FIRST(α)
   ```
3. Check that all predict sets for A are pairwise disjoint

### Why LL(1) Matters

LL(1) grammars can be parsed efficiently with:
- **No backtracking**: The parser makes the correct decision on the first look-ahead token
- **Linear time**: O(n) parsing time where n is the input length
- **Simple implementation**: Can be implemented with a recursive descent parser or parse table

### Converting to LL(1)

If a grammar is not LL(1), it can sometimes be transformed:

1. **Left Factoring**: Extract common prefixes
   ```
   A → αβ₁ | αβ₂  becomes  A → αA', A' → β₁ | β₂
   ```

2. **Left Recursion Elimination**: Remove left recursion
   ```
   A → Aα | β  becomes  A → βA', A' → αA' | ε
   ```

3. **Substitution**: Inline productions to eliminate conflicts

---

## Summary

**FIRST sets** tell us what terminals can start a derivation from a given symbol or sequence. They are computed bottom-up from terminals through non-terminals using fixed-point iteration.

**FOLLOW sets** tell us what terminals can appear after a non-terminal in any sentential form. They are computed using FIRST sets and propagate through the grammar.

Together, FIRST and FOLLOW sets enable:
- Construction of predictive parsers
- Grammar analysis and transformation
- Detection of LL(1) property
- Building efficient parse tables

The implementation in this framework provides efficient, correct computation of these sets for any context-free grammar, forming the foundation for top-down parsing algorithms.
