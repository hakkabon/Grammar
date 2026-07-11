//
//  RuleNotation.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/21.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation

/// Converts the Swift-DSL representation of a grammar (`[Rule]`, built via the
/// `Rule` / `Cat` / `Alt` / `Seq` / `Grp` / `Opt` result-builder types in
/// `RuleBuilder.swift`) into the same flat `[Production]` representation that
/// `StandardNotation` produces for text-based grammars (BNF/EBNF/WSN/generic).
///
/// The two are deliberately structural mirrors of one another:
///
/// | `Rule.Expression`   | `BnfExpression`              | Meaning                       |
/// |---------------------|------------------------------|-------------------------------|
/// | `.cat(a, b)`        | `.sequence([...])`           | implicit concatenation        |
/// | `.alt(a, b)`        | `.alternative([...])`        | choice — generates an aux NT  |
/// | `.seq(e)`           | `.repetition(e)`             | zero-or-more — aux NT         |
/// | `.grp(e)`           | `.grouping(e)`               | precedence only, no aux NT    |
/// | `.opt(e)`           | `.optional(e)`               | zero-or-one — aux NT          |
/// | `.sym(symbol)`      | `.terminal` / `.nonterminal` | already a resolved `Symbol`   |
/// | `.eps` / `.empty`   | `.empty`                     | epsilon, stored as `[]`       |
///
/// Unlike the text pipeline, `.sym(Symbol)` already carries a fully resolved
/// `Symbol` — including compiled `Terminal`s built inline via `rt(_:)`,
/// `lt(_:)`, etc. — so there is no separate `lexical { }` resolution pass:
/// whatever `Terminal` was attached at the call site is used as-is.
public struct RuleNotation {

    public init() {}

    /// - Parameter rules: The rules collected by a `@GrammarRuleBuilder` closure.
    /// - Returns: all productions reduced to BNF, and any newly generated
    ///   (synthetic) non-terminals — e.g. `@alt_3` for a nested alternative.
    public func rewrite(_ rules: [Rule]) -> (productions: [Production], generatedNonTerminals: Set<NonTerminal>) {
        var productions: [Production] = []
        var nonTerminals = Set<NonTerminal>()

        func addProduction(goal: NonTerminal, rule: [Symbol]) {
            productions.append(Production(goal: goal, rule: rule))
        }

        // Mirrors `StandardNotation`'s synthetic-nonterminal naming and reuses
        // the same shared `Counter`, so DSL-built grammars and text-imported
        // grammars can never collide even if combined in the same process.
        // Note: '@' denotes internal/synthetic.
        func generateNonterminal(withPrefix prefix: String) -> NonTerminal {
            var symbol = "@\(prefix)_\(Counter.next())"
            while nonTerminals.contains(NonTerminal(name: symbol)) {
                symbol = "@\(prefix)_\(Counter.next())"
            }
            return NonTerminal(name: symbol)
        }

        // `Alt { a; b; c }` builds a left-associated binary tree
        // `.alt(.alt(a, b), c)` (see `RuleAltBuilder.buildPartialBlock`);
        // flatten it back into an ordered list of branches.
        func alternatives(of expression: Rule.Expression) -> [Rule.Expression] {
            if case .alt(let lhs, let rhs) = expression {
                return alternatives(of: lhs) + alternatives(of: rhs)
            }
            return [expression]
        }

        /// Converts a `Rule.Expression` into a linear list of Symbols.
        /// If nested structures (alternation, optionality, repetition) are
        /// found, it generates synthetic productions as side effects and
        /// returns the new `NonTerminal` symbol in their place.
        func flatten(_ expression: Rule.Expression) -> [Symbol] {
            switch expression {
            case .sym(let symbol):
                return [symbol]

            case .eps, .empty:
                return []

            case .cat(let a, let b):
                return flatten(a) + flatten(b)

            // Nested alternation, e.g. A -> B (C | D) E.
            // Action: Create Aux. Aux -> C, Aux -> D. Return [B, Aux, E]
            case .alt:
                let auxGoal = generateNonterminal(withPrefix: "alt")
                nonTerminals.insert(auxGoal)
                for branch in alternatives(of: expression) {
                    addProduction(goal: auxGoal, rule: flatten(branch))
                }
                return [.nonTerminal(auxGoal)]

            // Repetition { ... } (zero or more, right-recursive).
            // Action: Create Aux. Aux -> B Aux, Aux -> ε. Return [Aux]
            case .seq(let e):
                let auxGoal = generateNonterminal(withPrefix: "rep")
                nonTerminals.insert(auxGoal)
                addProduction(goal: auxGoal, rule: flatten(e) + [.nonTerminal(auxGoal)])
                addProduction(goal: auxGoal, rule: [])
                return [.nonTerminal(auxGoal)]

            // Optional [ ... ].
            // Action: Create Aux. Aux -> B, Aux -> ε. Return [Aux]
            case .opt(let e):
                let auxGoal = generateNonterminal(withPrefix: "opt")
                nonTerminals.insert(auxGoal)
                addProduction(goal: auxGoal, rule: flatten(e))
                addProduction(goal: auxGoal, rule: [])
                return [.nonTerminal(auxGoal)]

            // Grouping only ever affects precedence while writing the DSL
            // itself; it never needs its own synthetic non-terminal — this
            // mirrors how `StandardNotation` handles `.grouping`.
            case .grp(let e):
                return flatten(e)
            }
        }

        for rule in rules {
            // A top-level alternation on a named rule becomes multiple
            // productions sharing that rule's own goal, exactly as
            // `StandardNotation` does for a `.production` body that is
            // `.alternative` — no synthetic non-terminal is needed since the
            // rule's own name already serves that role.
            for branch in alternatives(of: rule.rule) {
                addProduction(goal: rule.goal, rule: flatten(branch))
            }
        }

        return (productions, nonTerminals)
    }
}
