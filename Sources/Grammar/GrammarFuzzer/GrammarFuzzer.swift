//
//  GrammarFuzzer.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/12/17.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation

public struct GrammarFuzzer {
    
    public struct Options {
        let trace: Bool
        public init(trace: Bool = true) {
            self.trace = trace
        }
    }

    public struct ExpandConditions {
        let minNonTerminals: Int
        let maxNonTerminals: Int
        public init(minNonTerminals: Int = 1, maxNonTerminals: Int = 5) {
            self.minNonTerminals = minNonTerminals
            self.maxNonTerminals = maxNonTerminals
        }
    }

    public typealias Derivation = DerivationTree<NonTerminal, Terminal>
    
    let grammar: Grammar
    let options: Options
    let goalProductions: [NonTerminal:[Production]]
    
    public init(grammar: Grammar, options: Options = Options()) {
        self.grammar = grammar
        self.options = options
        self.goalProductions = Dictionary(grouping: self.grammar.productions, by: { $0.goal })
    }
}

extension GrammarFuzzer {

    func allRules(for nonTerminal: NonTerminal) -> [[Symbol]] {
        if let productions = goalProductions[nonTerminal] {
            return productions.map { $0.rule }
        }
        return []
    }

    func symbolCost(_ symbol: NonTerminal, seen: Set<NonTerminal>) -> Int {
        let rules = allRules(for: symbol)
        return minValue( rules.map { expansionCost($0, seen: seen.union([symbol])) } )
    }
    
    func expansionCost(_ symbols: [Symbol], seen: Set<NonTerminal>) -> Int {
        let nonTerminals = allNonTerminals(symbols: symbols)
        if nonTerminals.count == 0 {
            return 1
        }
        if seen.intersection(Set(nonTerminals)).count > 0 {
            return Int.max-10 // This causes integer overflow if not handled correctly.
        }
        return nonTerminals.map { symbolCost($0, seen: seen) }.reduce(0,+) + 1
    }
    
    /// Creates child nodes of each of the terminals and non-terminals contained in the given array.
    /// - Parameter symbols: expansion rule of one specific non-terminal
    /// - Returns: terminals and non-terminals rewritten as derivation nodes
    func expansionToChildren(symbols: [Symbol]) -> [Derivation] {
        return symbols.map { symbol in
            switch symbol {
            case let .terminal(terminal):
                return Derivation.leaf(terminal)
            case let .nonTerminal(nonTerminal):
                // `nil`, not `[]`: this is a fresh placeholder awaiting its own
                // expansion, not a node that has already resolved to ε. See the
                // discussion in DerivationTree.swift for why the distinction
                // matters — collapsing both into "empty children" is what made
                // grammars with epsilon/nullable non-terminals stall the fuzzer.
                return Derivation.node(nonTerminal, derivations: nil)
            case let .metaSymbol(meta): // any meta-symbols (EBNF) should be absent from the grammar at this point
                fatalError("resolve any meta symbols \(meta) in the grammar by lowering the grammar to standard form (BNF).")
            }
        }
    }

    /// Method returns `true` if the tree has any non-expanded nodes.
    ///
    /// A node with `derivations == nil` has not been expanded yet and is
    /// therefore still a possible expansion. A node with `derivations ==
    /// .some([])` has already been expanded — via an epsilon production —
    /// and derives nothing further, so it correctly falls through to
    /// `children.contains(where:)` over an empty collection, i.e. `false`.
    func anyPossibleExpansions(tree: Derivation) -> Bool {
        switch tree {
        case .leaf: return false
        case .node(_, nil): return true
        case let .node(_, .some(children)):
            return children.contains(where: { anyPossibleExpansions(tree: $0) })
        }
    }
    
    func possibleExpansions(node: Derivation) -> Int {
        switch node {
        case .leaf: return 0
        case .node(_, nil): return 1
        case let .node(_, .some(children)):
            return ( children.map{ possibleExpansions(node: $0) } ).reduce(0,+)
        }
    }

    /// Return index of subtree in `children` to be selected for expansion.
    /// Defaults to random.
    func chooseTreeExpansion(tree: Derivation, children: [Derivation]) -> Int {
        return Int.random(in: (0..<children.count))
    }

    /// Return index of expansion in `childrenAlternatives` to be selected.
    /// 'childrenAlternatives`: a list of possible children for `node`.
    /// Defaults to random. To be overloaded in subclasses.
    func chooseNodeExpansion(node: Derivation, childrenAlternatives: [[Derivation]]) -> Int {
        return Int.random(in: 0..<childrenAlternatives.count)
    }
    
    /// Process children after selection. By default, does nothing.
    func processChosenChildren(_ children: [Derivation], expansion: [Symbol]) -> [Derivation] {
        return children
    }

    /// Expands given non-terminal node with one production rule randomly chosen out of several possible grammar
    /// alternatives for given non-terminal.
    func expandNodeRandomly(node: Derivation) -> Derivation {
        guard case .node(let nonTerminal, nil) = node else {
            fatalError("assert node is unexpanded (derivations == nil) not valid")
        }

        // Fetch all possible expansions (derivations) from grammar...
        let expansions = allRules(for: nonTerminal)
        let childrenAlternatives: [[Derivation]] = expansions.map { expansionToChildren(symbols: $0) }
        
        // ... and select one random expansion (derivation)
        let index = chooseNodeExpansion(node: node, childrenAlternatives: childrenAlternatives)
        let chosenChildren = childrenAlternatives[index]
        // this function does not do anything yet
        let processedChildren = processChosenChildren(chosenChildren, expansion: expansions[index])

        return DerivationTree(nonTerminal, derivations: processedChildren)
    }

    /// Expands given non-terminal node with one production rule by applying given selection criteria to choose
    /// one among several possible grammar alternatives for given non-terminal.
    func expandNodeByCost(node: Derivation, choose: @escaping (([Int]) -> Int)) -> Derivation {
        guard case .node(let nonTerminal, nil) = node else {
            fatalError("assert node is unexpanded (derivations == nil) not valid")
        }
        // Fetch the possible expansions from grammar...
        let expansions = allRules(for: nonTerminal)

        // build triplet (children, cost, expansion)
        let childrenAlternativesWithCost = expansions.map {(
            children: expansionToChildren(symbols: $0),
            cost: expansionCost($0, seen: [nonTerminal]),
            expansion: $0)}

        let costs: [Int] = childrenAlternativesWithCost.map { $0.cost }
        let chosenCost = choose(costs) // min or max cost
        let childrenWithChosenCost = childrenAlternativesWithCost.compactMap { child, childCost, expansion in
            return childCost == chosenCost ? child : nil
        }
        let expansionWithChosenCost = childrenAlternativesWithCost.compactMap { child, childCost, expansion in
            return childCost == chosenCost ? expansion : nil
        }
        
        // if there are many candidates, which are of equal cost, choose one randomly
        let index = chooseNodeExpansion(node: node, childrenAlternatives: childrenWithChosenCost)
        let chosenChildren = childrenWithChosenCost[index]
        let chosenExpansion = expansionWithChosenCost[index]
        // this function does not do anything yet
        let processedChosenChildren = processChosenChildren(chosenChildren, expansion: chosenExpansion)

        return DerivationTree(nonTerminal, derivations: processedChosenChildren)
    }
    
    /// Choose an unexpanded symbol in tree and expand it.
    /// 1. Given tree-node contains only a non-terminal symbol which is expanded using given `expandMethod`.
    /// 2. Given tree-node contains unexpanded child nodes of which one is expanded using given `expandMethod`.
    func expandTreeOnce(_ tree: Derivation, expandMethod: @escaping (_: Derivation) -> Derivation) -> Derivation {
        switch tree {
        case .leaf:
            // Never reached in practice: callers only recurse into subtrees for
            // which `anyPossibleExpansions` returned true, and a leaf never does.
            return tree

        case .node(_, nil):
            // Not yet expanded: choose and apply a production for this node,
            // with one method of { expandNodeMaxCost | expandNodeMinCost | expandNodeRandomly }.
            return expandMethod(tree)

        case .node(_, .some(let children)) where children.isEmpty:
            // Already expanded via an epsilon production (derivations == .some([])).
            // It derives nothing further, so there is nothing to do here.
            return tree

        case .node(_, .some(let children)):
            // Find all children with possible expansions.
            let expandableChildren: [Derivation] = children.filter { anyPossibleExpansions(tree: $0) }

            // `index_map` translates an index in `expandable_children` back into the original index in `children`
            let indexMap: [Int] = children.enumerated().filter { child in expandableChildren.contains( where: { element -> Bool in
                child.element == element
            }) }.map { $0.offset }

            // Select a random child.
            let indexOfChildExpansion = chooseTreeExpansion(tree: tree, children: expandableChildren)

            // Expand in place with one method of { expandNodeMaxCost | expandNodeMinCost | expandNodeRandomly }.
            let expansion = expandTreeOnce(expandableChildren[indexOfChildExpansion], expandMethod: expandMethod)
            children[indexMap[indexOfChildExpansion]] = expansion

            return tree
        }
    }

    func expandNodeMinCost(_ node: Derivation) -> Derivation {
        if options.trace { print("Expanding ", currentExpansion(node), " at minimum cost") }
        return expandNodeByCost(node: node, choose: minValue)
    }
    
    func expandNodeMaxCost(_ node: Derivation) -> Derivation {
        if options.trace { print("Expanding ", currentExpansion(node), " at maximum cost") }
        return expandNodeByCost(node: node, choose: maxValue)
    }
    
    /// Expand tree using `expandNodeMethod` as node expansion function until the number of possible
    /// expansions reaches `limit`.
    func expandTreeWithStrategy(_ tree: Derivation, expandMethod: @escaping (_: Derivation) -> Derivation, limit: Int = 0) -> Derivation {
        var tree = tree
        while ((limit == 0) || (possibleExpansions(node: tree) < limit)) && anyPossibleExpansions(tree: tree) {
            tree = expandTreeOnce(tree, expandMethod: expandMethod)
            if options.trace { print(tree) }
        }
        return tree
    }

    /// Produce a string from the given `grammar`.
    /// - Parameters:
    ///   - nonTerminal: any non-terminal symbol in the grammar used as starting point of the grammar expansion.
    ///   - conditions: limits the number of symbols allowed to expand the grammar.
    /// - Returns: Random expansion of the given start non-terminal applied on the given grammar.
    public func fuzz(start startSymbol: NonTerminal, conditions: ExpandConditions = ExpandConditions()) -> Derivation {

        // We can now put all three phases together in a single function which will work as follows:
        // Max cost expansion - Expand the tree using expansions with maximum cost until we have at least
        // `minNonTerminals` nonterminals. This phase can be easily skipped by setting min_nonterminals to zero.
        // Random expansion - Keep on expanding the tree randomly until we reach `maxNonTerminals` nonterminals.
        // Min cost expansion - Close the expansion with minimum cost.
        //
        // We implement these three phases by having `expandNode` reference the expansion method to apply. This is
        // controlled by setting `expandNode` (the method reference) to first `expandNodeMaxCost` (i.e., calling
        // `expandNode()` invokes `expandNodeMaxCost()`), then `expandNodeRandomly`, and finally `expandNodeMinCost`.
        // In the first two phases, we also set a maximum limit of `minNonterminals` and `maxNonterminals`, respectively.
        //
        
        // Ensure that `startSymbol` is a valid non-terminal, otherwise fallback to grammar.start.
        let validStartSymbol = grammar.nonTerminals.contains(startSymbol) ? startSymbol : grammar.start
        var derivationTree = Derivation(validStartSymbol)
        derivationTree = expandTreeWithStrategy(derivationTree, expandMethod: expandNodeMaxCost, limit: conditions.minNonTerminals)
        derivationTree = expandTreeWithStrategy(derivationTree, expandMethod: expandNodeRandomly, limit: conditions.maxNonTerminals)
        derivationTree = expandTreeWithStrategy(derivationTree, expandMethod: expandNodeMinCost)
        assert(possibleExpansions(node: derivationTree) == 0)
        
        return derivationTree
    }
    
    func allNonTerminals(symbols: [Symbol]) -> [NonTerminal] {
        return symbols.compactMap { symbol -> NonTerminal? in
            guard case .nonTerminal(let nonTerminal) = symbol else {
                return nil
            }
            return nonTerminal
        }
    }

    func countNonTerminals(symbols: [Symbol]) -> Int {
        return symbols.reduce(0) { partialResult, symbol in
            if case .nonTerminal = symbol {
                return partialResult + 1
            }
            return partialResult
        }
    }
    
    /// Returns the non-terminal in the given derivation node.
    /// - Parameter tree: given derivation node
    /// - Returns: name of non-terminal in the given derivation node
    func currentExpansion(_ node: Derivation) -> String {
        switch node {
        case .leaf(let terminal): return "\(terminal)"
        case .node(let nonTerminal, derivations:_): return "<\(nonTerminal)>"
        }
    }
    
    func minValue(_ array: [Int]) -> Int {
        guard array.count > 0 else { fatalError("min value of array is undefined caused by a zero length array") }
        var currentMin = array[0]
        for value in array[1..<array.count] {
            if value < currentMin {
                currentMin = value
            }
        }
        return currentMin
    }
    
    func maxValue(_ array: [Int]) -> Int {
        guard array.count > 0 else { fatalError("max value of array is undefined caused by a zero length array") }
        var currentMax = array[0]
        for value in array[1..<array.count] {
            if value > currentMax {
                currentMax = value
            }
        }
        return currentMax
    }
}
