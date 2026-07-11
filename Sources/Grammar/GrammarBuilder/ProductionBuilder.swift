//
//  ProductionBuilder.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/21.
//

import Foundation

// This file previously held an early, entirely-commented-out draft of `Rule`
// (superseded by the `Rule` in `RuleBuilder.swift`) plus a `generate(goal:builder:)`
// helper that duplicated what `RuleNotation.rewrite(_:)` now does properly.
// The `@ProductionBuilder`/`ProductionResult` mini-DSL that draft depended on
// still exists in `GrammarBuilders.swift`/`ProductionResult.swift` and is used
// by `Production.init(goal:builder:)`, but is otherwise unused elsewhere in
// this module — see the `GrammarBuilder` review notes for whether it's worth
// keeping two independent EBNF-composition DSLs (`Rule`/`Cat`/`Alt`/... vs.
// `ProductionResult`/`<+>`/`<|>`) side by side long-term.
