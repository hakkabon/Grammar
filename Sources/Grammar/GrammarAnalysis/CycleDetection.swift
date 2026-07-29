//
//  CycleDetection.swift
//  Crammar
//
//  Created by Ulf Akerstedt-Inoue on 2025/10/08.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation

extension Grammar {

    /// Detects if there is a cycle in the grammar's non-terminal dependencies.
    /// - Returns: An array of cycles, where each cycle is a path of non-terminals.
    public func detectCycles() -> [[Symbol]] {
        var cycles: [[Symbol]] = []
        let nonTerminals = self.nonTerminals.map { Symbol.nonTerminal($0) }

        // Use a color system to track visited nodes during DFS
        var visited: Set<Symbol> = []
        var recursionStack: Set<Symbol> = []
        
        // Iterate through all non-terminals to find all cycles
        for nonTerminal in nonTerminals {
            if !visited.contains(nonTerminal) {
                var path: [Symbol] = []
                findCyclesDFS(nonTerminal: nonTerminal,
                              visited: &visited,
                              recursionStack: &recursionStack,
                              path: &path,
                              cycles: &cycles)
            }
        }
        return cycles
    }

    /// The recursive DFS helper function for cycle detection.
    private func findCyclesDFS(nonTerminal: Symbol,
                               visited: inout Set<Symbol>,
                               recursionStack: inout Set<Symbol>,
                               path: inout [Symbol],
                               cycles: inout [[Symbol]]) {
        
        visited.insert(nonTerminal)
        recursionStack.insert(nonTerminal)
        path.append(nonTerminal)

        let groupedProductions = Dictionary(grouping: Array(self.productions), by: \.goal)
        if case let .nonTerminal(nt) = nonTerminal {
            if let productions = groupedProductions[nt] {
                for production in productions {
                    for symbol in production.rule {
                        guard case .nonTerminal(_) = symbol else { continue }
                        if !visited.contains(symbol) {
                            findCyclesDFS(nonTerminal: symbol,
                                          visited: &visited,
                                          recursionStack: &recursionStack,
                                          path: &path,
                                          cycles: &cycles)
                        } else if recursionStack.contains(symbol) {
                            // Back edge detected, which means a cycle exists
                            if let cycleStart = path.firstIndex(of: symbol) {
                                let cycle = Array(path[cycleStart...])
                                cycles.append(cycle)
                            }
                        }
                    }
                }
            }
        }
        
        path.removeLast()
        recursionStack.remove(nonTerminal)
    }
}
