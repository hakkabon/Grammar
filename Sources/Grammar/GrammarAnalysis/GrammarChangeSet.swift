import Foundation

/// A deterministic semantic delta between two grammar artifacts.
///
/// Production invalidation is transitive over nonterminal references: changing
/// a production for `B` also invalidates retained productions whose goals can
/// reach `B`. Lexical changes conservatively require retokenization and
/// invalidate every old production because token boundaries may have changed.
public struct GrammarChangeSet: Hashable, Codable, Sendable {
    public let sourceFingerprint: String
    public let targetFingerprint: String
    public let startSymbolChanged: Bool
    public let requiresRetokenization: Bool
    public let addedProductionIDs: [GrammarProductionID]
    public let removedProductionIDs: [GrammarProductionID]
    public let retainedProductionIDs: [GrammarProductionID]
    public let invalidatedProductionIDs: [GrammarProductionID]
    public let affectedNonterminalNames: [String]
    public let changedLexicalRuleNames: [String]

    public var isEmpty: Bool { sourceFingerprint == targetFingerprint }
    public var invalidatedProductionIDSet: Set<GrammarProductionID> {
        Set(invalidatedProductionIDs)
    }

    public init(from source: Grammar, to target: Grammar) {
        sourceFingerprint = source.incrementalSemanticFingerprint
        targetFingerprint = target.incrementalSemanticFingerprint
        startSymbolChanged = source.start != target.start

        let sourceProductions = Dictionary(
            source.productions.map { (GrammarProductionID($0), $0) },
            uniquingKeysWith: { first, _ in first })
        let targetProductions = Dictionary(
            target.productions.map { (GrammarProductionID($0), $0) },
            uniquingKeysWith: { first, _ in first })
        let sourceIDs = Set(sourceProductions.keys)
        let targetIDs = Set(targetProductions.keys)
        addedProductionIDs = targetIDs.subtracting(sourceIDs).sorted()
        removedProductionIDs = sourceIDs.subtracting(targetIDs).sorted()
        retainedProductionIDs = sourceIDs.intersection(targetIDs).sorted()

        let sourceLexical = source.incrementalLexicalRuleKeys
        let targetLexical = target.incrementalLexicalRuleKeys
        let lexicalNames = Set(sourceLexical.keys).union(targetLexical.keys)
        let changedLexical = lexicalNames.filter {
            sourceLexical[$0] != targetLexical[$0]
        }
        let orderChanged = source.incrementalLexicalRuleOrder
            != target.incrementalLexicalRuleOrder
        changedLexicalRuleNames = (orderChanged ? lexicalNames : changedLexical).sorted()
        requiresRetokenization = !changedLexicalRuleNames.isEmpty

        let allProductions = Array(sourceProductions.values) + Array(targetProductions.values)
        let allNonterminals = Set(allProductions.flatMap {
            [$0.goal.name] + $0.generatedNonTerminals.map(\.name)
        })
        var affected = Set<String>()
        if startSymbolChanged || requiresRetokenization {
            affected = allNonterminals
        } else {
            for identity in Set(addedProductionIDs + removedProductionIDs) {
                if let production = sourceProductions[identity] ?? targetProductions[identity] {
                    affected.insert(production.goal.name)
                }
            }

            var reverse: [String: Set<String>] = [:]
            for production in allProductions {
                for dependency in production.generatedNonTerminals {
                    reverse[dependency.name, default: []].insert(production.goal.name)
                }
            }
            var work = Array(affected)
            while let changed = work.popLast() {
                for parent in reverse[changed, default: []]
                    where affected.insert(parent).inserted {
                    work.append(parent)
                }
            }
        }
        affectedNonterminalNames = affected.sorted()
        invalidatedProductionIDs = sourceProductions.compactMap { identity, production in
            affected.contains(production.goal.name) ? identity : nil
        }.sorted()
    }
}

public extension Grammar {
    func changeSet(to target: Grammar) -> GrammarChangeSet {
        GrammarChangeSet(from: self, to: target)
    }

    /// Stable content fingerprint used to bind reusable engine state to a
    /// grammar revision without relying on process-randomized hashing.
    var incrementalSemanticFingerprint: String {
        let productions = self.productions.map(GrammarProductionID.init)
            .sorted().map { GrammarProductionID.frame($0.rawValue) }.joined()
        let lexical = incrementalLexicalRuleOrder.compactMap { name in
            incrementalLexicalRuleKeys[name].map {
                GrammarProductionID.frame(name) + GrammarProductionID.frame($0)
            }
        }.joined()
        return "grammar-v1;S\(GrammarProductionID.frame(start.name));P"
            + GrammarProductionID.frame(productions) + ";L"
            + GrammarProductionID.frame(lexical)
    }

    fileprivate var incrementalLexicalRuleOrder: [String] {
        lexicalSpecification.rules.map(\.name)
            + lexicalTokens.keys.filter {
                lexicalSpecification[$0] == nil
            }.sorted()
    }

    fileprivate var incrementalLexicalRuleKeys: [String: String] {
        var result = Dictionary(uniqueKeysWithValues: lexicalSpecification.rules.map {
            ($0.name, "\($0.channel.rawValue):\($0.priority):\($0.matcher.displaySource)")
        })
        for (name, terminal) in lexicalTokens where result[name] == nil {
            result[name] = "legacy:\(terminal.incrementalIdentityKey)"
        }
        return result
    }
}
