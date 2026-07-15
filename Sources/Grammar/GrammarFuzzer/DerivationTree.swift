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
///                     .node(symbol: "<expr>", derivations: []),
///                     .leaf("+"),
///                     .node(symbol: "<term>", derivations: [])
///                   ])
///           ])
///```
public enum DerivationTree<Node: Equatable, Leaf: Equatable> {
    /// Node without children storing a value element
    case leaf(Leaf)
    
    /// Node with a symbol and a list of arbitrary recursively nested tree structures
    // indirect case node(Node, derivations: [DerivationTree<Node,Leaf>])
    indirect case node(Node, derivations: MutableList<DerivationTree<Node,Leaf>>)
}

extension DerivationTree {
    
    public init(_ value: Leaf) {
        self = .leaf(value)
    }

    public init(_ symbol: Node) {
        self = .node(symbol, derivations: [])
    }
    
    public init(_ symbol: Node, derivation: DerivationTree<Node,Leaf>) {
        self = .node(symbol, derivations: MutableList(arrayLiteral: derivation))
    }

    public init(_ symbol: Node, derivations: [DerivationTree<Node,Leaf>]) {
        let mutableList: MutableList<DerivationTree<Node,Leaf>> = MutableList()
        derivations.forEach { mutableList.append($0) }
        self = .node(symbol, derivations: mutableList)
    }

    /// All leafs of the tree
    public var leafs: [Leaf] {
        switch self {
        case .leaf(let leaf):
            return [leaf]
        case .node(_, derivations: let derivations):
            return derivations.flatMap{ $0.leafs }
        }
    }
}

extension DerivationTree: Equatable {
    
    public static func == (lhs: DerivationTree<Node,Leaf>, rhs: DerivationTree<Node,Leaf>) -> Bool {
        switch (lhs, rhs) {
        case let (.leaf(lValue), .leaf(rValue)):
            return lValue == rValue
        case (let .node(lSymbol, derivations: lDerivation), let .node(rSymbol, derivations: rDerivation)):
            return lSymbol == rSymbol && lDerivation.count == rDerivation.count && !zip(lDerivation, rDerivation).map(==).contains(false)
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
        case let .node(symbol, derivations):
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
            if case let .node(_,derivations) = node {
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
