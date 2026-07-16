//
//  DerivationTree.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/12/09.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation
import TerminalColors

/// A tree which stores terminal values in its leafs.
///
/// - leaf: A leaf node holding a leaf value
/// - node: A node with a key and an arbitrary list of node elements
///
///```
/// var derivation: DerivationTree =
///     .node(symbol: "<start>",
///           derivations: [
///             .node(symbol: "<expr>",
///                   derivations: [
///                     .node(symbol: "<expr>", derivations: nil),
///                     .leaf("+"),
///                     .node(symbol: "<term>", derivations: [])
///                   ])
///           ])
///```
///
/// ## Unexpanded nodes vs. epsilon (empty) expansions
///
/// A `.node` goes through two meaningfully different states over its
/// lifetime, and `derivations` distinguishes them by being `nil` in the
/// first state and non-`nil` (possibly empty) in the second:
///
/// - `derivations == nil`  — the node has been created (e.g. as a
///   placeholder child while expanding its parent) but no production has
///   been chosen for it yet. It still needs to be expanded.
/// - `derivations == .some([...])` — a production has been chosen and
///   applied. If the chosen production's rule was itself empty (an epsilon
///   production, `A ::= ε`), this is `.some([])`: the node is fully
///   resolved and derives nothing further, which is different from "not
///   expanded yet" even though both have zero children.
///
/// Collapsing these two states into a single "children.count == 0" test (as
/// an earlier version of this type did, using a non-optional, always-empty
/// list for both) made a node that legitimately derives ε indistinguishable
/// from one that simply hasn't been visited yet. Any traversal driven by
/// that test — most importantly `GrammarFuzzer`'s `anyPossibleExpansions`/
/// `possibleExpansions` — would therefore treat an epsilon-resolved node as
/// perpetually still-expandable: re-selecting it, re-applying its only
/// (empty) production, and never converging, since the result looked
/// identical to the input. For a grammar containing any nullable
/// non-terminal (`A ::= ε`, or transitively nullable through other
/// non-terminals), this hung the fuzzer's final, unbounded closing phase
/// (`expandNodeMinCost`, called with no expansion limit) indefinitely. Using
/// `Optional` makes the third state explicit instead of overloading zero
/// children to mean two different things.
public enum DerivationTree<Node: Equatable, Leaf: Equatable> {
    /// Node without children storing a value element
    case leaf(Leaf)
    
    /// Node with a symbol and a list of arbitrary recursively nested tree structures.
    /// `nil` means "not yet expanded"; `.some([])` means "expanded via an epsilon
    /// production and therefore derives nothing further". See the type-level
    /// documentation above.
    // indirect case node(Node, derivations: [DerivationTree<Node,Leaf>])
    indirect case node(Node, derivations: MutableList<DerivationTree<Node,Leaf>>?)
}

extension DerivationTree {
    
    public init(_ value: Leaf) {
        self = .leaf(value)
    }

    /// Creates a fresh, not-yet-expanded node for `symbol`. No production has
    /// been chosen yet, so `derivations` is `nil` rather than an empty list —
    /// see the type-level documentation for why that distinction matters.
    public init(_ symbol: Node) {
        self = .node(symbol, derivations: nil)
    }
    
    public init(_ symbol: Node, derivation: DerivationTree<Node,Leaf>) {
        self = .node(symbol, derivations: MutableList(arrayLiteral: derivation))
    }

    /// Creates an already-expanded node for `symbol` with the given children.
    /// Passing an empty array here (as opposed to using `init(_:)`) records
    /// that `symbol` was expanded via an epsilon production and deliberately
    /// derives nothing further, distinct from a node that hasn't been
    /// expanded at all.
    public init(_ symbol: Node, derivations: [DerivationTree<Node,Leaf>]) {
        let mutableList: MutableList<DerivationTree<Node,Leaf>> = MutableList()
        derivations.forEach { mutableList.append($0) }
        self = .node(symbol, derivations: mutableList)
    }

    /// All leafs of the tree. An unexpanded node (`derivations == nil`)
    /// contributes no leafs yet.
    public var leafs: [Leaf] {
        switch self {
        case .leaf(let leaf):
            return [leaf]
        case .node(_, derivations: let derivations):
            return derivations?.flatMap { $0.leafs } ?? []
        }
    }
}

extension DerivationTree: Equatable {
    
    public static func == (lhs: DerivationTree<Node,Leaf>, rhs: DerivationTree<Node,Leaf>) -> Bool {
        switch (lhs, rhs) {
        case let (.leaf(lValue), .leaf(rValue)):
            return lValue == rValue
        case (let .node(lSymbol, derivations: lDerivation), let .node(rSymbol, derivations: rDerivation)):
            guard lSymbol == rSymbol else { return false }
            switch (lDerivation, rDerivation) {
            case (nil, nil):
                return true
            case let (l?, r?):
                return l.count == r.count && !zip(l, r).map(==).contains(false)
            default:
                // One side is unexpanded (nil) and the other has already been
                // expanded (even to `.some([])`) — these are different states.
                return false
            }
        default:
            return false
        }
    }
}

extension DerivationTree: CustomStringConvertible {

    public var description: String {
        return DerivationTreePrinter.print(self)
    }
}

// MARK: - Tree outline for pretty printing
extension DerivationTree {
    
    public var treeStructure: String {
        return treeLines().joined(separator:"\n")
    }
    
    func treeLines(_ nodeIndent: String = "", _ childIndent: String = "") -> [String] {
        switch self {
        case let .leaf(value):
            return [ nodeIndent + "\(value)" ]
        case let .node(symbol, optionalDerivations):
            guard let derivations = optionalDerivations, !derivations.isEmpty else {
                // Either not yet expanded (nil) or resolved to ε (empty, non-nil).
                return [ nodeIndent + "\(symbol)" ]
            }
            return [ nodeIndent + "\(symbol)" ] + derivations.enumerated()
                .map{ ($0 < derivations.count-1, $1) }
                .flatMap{ $0 ? $1.treeLines("┣╸","┃ ") : $1.treeLines("┗╸","  ") }
                .map{ childIndent + $0 }
        }
    }
    
    public func printStructure(indentation spaces: Int = 2) {
        let tab = Array(repeating: " ", count: spaces).joined()
        
        func traverseStructure(_ node: DerivationTree, indentation space: String = "", visitor: (DerivationTree,String) -> ()) {
            visitor(node, space)
            if case let .node(_,derivations) = node, let derivations {
                for derivation in derivations {
                    traverseStructure(derivation, indentation: space + tab, visitor: visitor)
                }
            }
        }
        
        traverseStructure(self, indentation: "", visitor: { (node,indent) in
            print(indent + "\(node)")
        })
    }
}
