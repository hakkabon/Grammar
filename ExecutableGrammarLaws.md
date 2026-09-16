# Executable grammar laws

Grammar 0.3.1 adds executable metamorphic witnesses to the normalized grammar
contract. A witness contains both normalized models and a declaration of the
relationship that produced the candidate. Construction fails unless the
transformation is structurally exact.

Two schema-1 laws are initially supported:

- `productionPermutation` changes declaration order while retaining every
  production occurrence and identity exactly once;
- `nonterminalAlphaRenaming` applies a collision-free bijection to the start
  symbol, production left- and right-hand sides, and generated nonterminals.

```swift
let orderWitness = try GrammarLawTransformer.permuteProductions(
    model,
    order: model.productions.map(\.id).reversed(),
    id: "reverse-production-order"
)

let renameWitness = try GrammarLawTransformer.alphaRenameNonterminals(
    model,
    renames: [.init(from: "Expression", to: "Formula")],
    id: "rename-expression"
)
```

`GrammarLawVerifier` proves only that the candidate is the declared structural
transformation. It does not run a parser or claim language equivalence. Parser
owns executable observation laws over these pairs; parser engines own the
actual executions.

The serialized contract is published in
`Schemas/ExecutableGrammarLaw.schema.json`. Future laws require an explicit
schema-compatible addition rather than interpreting arbitrary source rewrites
as equivalent grammars.
