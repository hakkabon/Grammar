//
//  DerivationTreePrinter.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2026/07/14.
//  Copyright © 2026 hakkabon software. All rights reserved.
//

import Foundation
import TerminalColors

struct DerivationTreePrinter {
    
    // ANSI Terminal Colors
    private static let branchColor = TerminalColor(fg: .blue)
    private static let leafColor = TerminalColor(fg: .green)
    private static let nodeColor = TerminalColor(fg: .cyan1, .bold)
    
    /// Generates a visual tree structure string from the DerivationTree. Starting at its root node
    /// travering all its children (all intermediate nodes down towards its leafs).
    static func print<N, L>(_ tree: DerivationTree<N, L>, indentation: String = "", isLast: Bool = true) -> String {
        switch tree {
        case .leaf(let value):
            return "\(indentation)\("\(value)", color: leafColor)\n"
            
        case .node(let value, let children):
            var result = "\(indentation)\("\(value)", color: nodeColor)\n"
            
            for (index, child) in children.enumerated() {
                let isLastChild = index == children.count - 1
                result += printChildren(child, prefix: indentation, isLast: isLastChild)
            }
            return result
        }
    }

    /// Generates a visual tree structure from the given DerivationTree (subtree). The given subtree is
    /// processed, which is a leaf node or an intermediate node with its children.
    static func printChildren<N, L>(_ tree: DerivationTree<N, L>, prefix: String = "", isLast: Bool = true) -> String {
        let marker = isLast ? "└── " : "├── "
        let currentPrefix = "\(prefix, color: branchColor)\(marker, color: branchColor)"
        
        switch tree {
        case .leaf(let value):
            return "\(currentPrefix)\("\(value)", color: leafColor)\n"
            
        case .node(let value, let children):
            var result = "\(currentPrefix)\("\(value)", color: nodeColor)\n"
            
            // Prepare prefix for children
            // If this is the last node, the vertical bar "│" stops here.
            // Otherwise, it continues down to connect to the next sibling.
            let childPrefix = prefix + (isLast ? "    " : "\("│   ", color: branchColor)")
            
            for (index, child) in children.enumerated() {
                let isLastChild = index == children.count - 1
                result += printChildren(child, prefix: childPrefix, isLast: isLastChild)
            }
            return result
        }
    }
}
