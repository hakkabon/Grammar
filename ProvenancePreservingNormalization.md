# Provenance-preserving grammar normalization

`Grammar.normalizationReport(to:productionIDs:)` is the versioned boundary for
normal-form consumers. It runs the same standard, Chomsky, or Greibach pipeline
used by `grammarForm`, but returns an immutable parser-facing model together
with a total ancestry relation.

Every emitted production has a deterministic `n1`, `n2`, … identity and at
least one source `GrammarProductionID`. Unchanged rules have `exact` provenance.
When epsilon removal, unit substitution, shared terminal wrappers, binarization,
or Greibach substitution combines ancestry, the report deliberately labels the
result `conservative`: its source IDs are the complete reachable source closure,
not a fabricated one-to-one origin.

```swift
let report = try grammar.normalizationReport(
    to: .chomsky,
    productionIDs: durableSourceIDs
)
precondition(report.preservesCompleteProvenance)
```

The report schema version is independent of `GrammarNormalizedModel`. Reports
are `Codable`, `Hashable`, and `Sendable`, include the ordered pipeline stages,
and preserve synthetic nonterminal identities in the output model. CNF and GNF
output ordering is deterministic across runs. Schema 1 is published in
`Schemas/NormalizationReport.schema.json`.

This contract is intentionally owned by Grammar. Parser engines may project it
into engine-specific rule types, but must retain output production identities
and ancestry. CYK's local converter can now be migrated incrementally; deletion
of that converter belongs after its tree reconstruction consumes this evidence.
