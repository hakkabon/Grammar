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
    func allNullableNonTerminals() -> Set<NonTerminal> {
        var nullable: Set<NonTerminal> = []

        // Seed: direct epsilon productions
        for p in productions where p.isNullable {
            nullable.insert(p.goal)
        }

        // Fixed-point algorithm: A is nullable if all symbols in some rhs are nullable
        var changed = true
        while changed {
            changed = false
            for p in productions where !p.isNullable {
                guard !nullable.contains(p.goal) else { continue }
                let allNullable = p.rule.allSatisfy { symbol in
                    if case .nonTerminal(let nt) = symbol { return nullable.contains(nt) }
                    if case .terminal(.meta(.eps)) = symbol { return true }
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
}
