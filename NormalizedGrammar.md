# Normalized grammar and analysis contract

`GrammarNormalizedModel` is Grammar's versioned, engine-neutral handoff to
Parser, parser engines, Grammar-REPL, and application adapters. It is additive;
the existing `Grammar`, `Production`, and analysis APIs remain source compatible.

## Invariants

- Production order and duplicate occurrences are preserved.
- Every production carries a non-empty, unique `GrammarProductionID`.
- An empty right-hand side is the only representation of epsilon.
- EBNF meta-symbols must be lowered before a model can be created.
- Literal, literal-list, character-range, regular-expression, and boundary
  terminals remain structurally distinct.
- Lexical definitions, generated nonterminals, precedence levels, epsilon, and
  end-of-input conventions travel with the model.
- Schema 1 has an explicit JSON representation in
  `Schemas/NormalizedGrammar.schema.json`; production IDs encode as strings and
  symbols and terminals use explicit `kind` discriminators.

`Grammar.normalizedModel()` assigns deterministic occurrence IDs (`p1`, `p2`,
...). These are stable for an unchanged production sequence. A source editor or
conformance corpus that owns durable identities supplies them through
`productionIDs:` instead.

```swift
let model = try grammar.normalizedModel(productionIDs: corpusProductionIDs)
let analysis = model.analyze()
```

## Analysis snapshot

`GrammarNormalizedAnalysis` contains sorted, reproducible observations for:

- defined, referenced, undefined, reachable, and productive nonterminals;
- nullability and direct or component-level recursion;
- nonterminal dependency edges and duplicate production occurrences;
- unused lexical definitions;
- FIRST and FOLLOW lookaheads with explicit epsilon and end-of-input values;
- pairwise LL(1) prediction conflicts tied to production identities.

`isLL1` requires defined references, no recursive component, and no predictive
table conflict. Analysis never discards an invalid or unreachable declaration;
it reports it so interactive tools can explain the grammar faithfully.

## Deliberate boundary

The normalized model describes grammar semantics, not source presentation.
Source spans and lowering origins stay in authoring adapters, while parse-tree
nodes and forests stay in Parser. The next ecosystem adoption step can therefore
attach Workbench source identities to this model without moving editor concerns
into Grammar.
