# Grammar-form state transitions

`Grammar.grammarForm` is a compatibility API whose property observer rewrites
`productions` and `generatedNonTerminals` when it is assigned `.standard`,
`.chomsky`, or `.greibach`. The new characterization suite verifies that each
direct transition from an imported grammar agrees with the corresponding pure
conversion pipeline and survives Codable round trips. The transition also
recomputes `nullableNonTerminals`; previously that stored analysis described
the productions from before the mutation.

Assigning `.none` is deliberately characterized as a no-op. It changes the
label but does not restore productions that were replaced by an earlier
transition. Callers that need to retain several representations should keep the
source grammar and use `rewriteToStandardForm()`, `toChomskyNormalForm()`, or
`toGreibachNormalForm()` to create explicit values instead of treating
`grammarForm` as reversible storage.

## Remaining ownership debt

Grammar owns public CNF and GNF transformations. CYK-Parser still contains an
independent `CNFConverter` because it emits engine-specific `CNFRule` values
and generated-name conventions that `TreeTransformer` uses to reconstruct
natural trees. Removing that duplication safely requires the shared
normalization-result contract now published by Grammar. It contains:

- normalized productions and generated-symbol identity;
- source-production provenance for every introduced rule;
- terminal-wrapper and binarization mappings; and
- enough information to project packed CYK results back to original trees.

The dependency-first follow-up is to verify language preservation and tree
reconstruction against the shared corpus, migrate CYK-Parser to the report, and
only then delete CYK's converter. See
[Provenance-preserving grammar normalization](ProvenancePreservingNormalization.md).
The Phase 20 study-explorer work does not change either normalization algorithm.
