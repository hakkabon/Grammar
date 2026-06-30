//
//  Nullable.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/09.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation
import OSLog

extension Grammar {
    
    // Compute the set of nullable non-terminals: { A in V | A =>* eps }
    // A non-terminal is nullable if it can derive the empty string.
    // Basis:
    //     All non-terminals appearing on the left-hand side of a production of the
    //     form A→ϵ are nullable.
    // Induction:
    //     If non-terminal B→α and all symbols appearing in α are variables that have
    //     been marked as nullable, then B is nullable.
    // Apply step 2 until no more variables can be marked as nullable.
    public func allNullableNonTerminals() -> Set<NonTerminal> {
        var nullable: Set<NonTerminal> = []

        // Seed: direct epsilon productions
        for p in productions where p.isNullable {
            nullable.insert(p.goal)
        }

        // Fixed-point algorithm: A is nullable if all symbols in some rhs are nullable
        //
        // Note: every `p` reaching this loop has `!p.isNullable`, which (since
        // `Production` normalizes every rule at creation) means `p.rule` is
        // guaranteed to be non-empty and free of epsilon-equivalent terminal
        // symbols — there is no longer a literal epsilon symbol to look for
        // inside a rule, only the rule being empty (`rule == []`), which is
        // already handled by the seeding loop above.
        var changed = true
        while changed {
            changed = false
            for p in productions where !p.isNullable {
                guard !nullable.contains(p.goal) else { continue }
                let allNullable = p.rule.allSatisfy { symbol in
                    if case .nonTerminal(let nt) = symbol { return nullable.contains(nt) }
                    return false
                }
                if allNullable {
                    nullable.insert(p.goal)
                    changed = true
                }
            }
        }
        
        return nullable
    }
    
    /// Check if a sequence of symbols can derive ε
    public func isNullable(_ symbols: [Symbol]) -> Bool {
        symbols.allSatisfy { symbol in
            switch symbol {
            case .terminal:
                return false
            case .nonTerminal(let nt):
                return nullableNonTerminals.contains(nt)
            case .metaSymbol:
                return false
            }
        }
    }
    
    /// Check if a nonterminal can derive ε
    public func isNullable(_ nt: NonTerminal) -> Bool {
        return nullableNonTerminals.contains(nt)
    }
}
