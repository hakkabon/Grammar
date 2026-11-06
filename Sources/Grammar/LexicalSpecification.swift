import Foundation

/// Whether a lexical rule produces parser input or retained trivia.
public enum LexicalChannel: String, Codable, Hashable, Sendable {
    case significant
    case trivia
}

/// A declarative matcher in a language grammar's `lexical { ... }` block.
///
/// Literal and delimited matchers deliberately avoid encoding keywords and
/// comments as assertion-heavy regular expressions. This keeps the grammar
/// readable and gives incremental scanners explicit restart-state semantics.
public enum LexicalMatcher: Codable, Hashable, Sendable {
    case literal(String)
    case regularExpression(String)
    case characterRange(String, String)
    case literals([String])
    case lineComment(String)
    case blockComment(open: String, close: String)

    public var displaySource: String {
        switch self {
        case .literal(let value): return "\"\(value)\""
        case .regularExpression(let pattern): return "/\(pattern)/"
        case .characterRange(let lower, let upper):
            return "\"\(lower)\" .. \"\(upper)\""
        case .literals(let values):
            return values.map { "\"\($0)\"" }.joined(separator: " | ")
        case .lineComment(let prefix): return "lineComment(\"\(prefix)\")"
        case .blockComment(let open, let close):
            return "blockComment(\"\(open)\", \"\(close)\")"
        }
    }

    /// The Grammar terminal used when this rule is referenced by a production.
    /// Trivia and delimited constructs need not appear in productions.
    public var terminal: Terminal? {
        switch self {
        case .literal(let value): return Terminal(list: [value])
        case .regularExpression(let pattern): return try? Terminal(expression: pattern)
        case .characterRange(let lower, let upper):
            guard lower.count == 1, upper.count == 1,
                  let first = lower.first, let last = upper.first, first <= last else {
                return nil
            }
            return Terminal(range: first ... last)
        case .literals(let values): return Terminal(list: values)
        case .lineComment, .blockComment: return nil
        }
    }
}

/// One named lexical declaration. Declaration order is significant: it is the
/// stable tie-break after maximal munch and explicit priority.
public struct LexicalRuleDefinition: Codable, Hashable, Sendable, Identifiable {
    public let name: String
    public let matcher: LexicalMatcher
    public let channel: LexicalChannel
    public let priority: Int

    public var id: String { name }

    public init(name: String, matcher: LexicalMatcher,
                channel: LexicalChannel = .significant, priority: Int = 0) {
        precondition(!name.isEmpty)
        self.name = name
        self.matcher = matcher
        self.channel = channel
        self.priority = priority
    }
}

/// The executable lexical half of a grammar artifact.
public struct LexicalSpecification: Codable, Hashable, Sendable {
    public let rules: [LexicalRuleDefinition]

    public static let empty = LexicalSpecification(rules: [])

    public init(rules: [LexicalRuleDefinition]) {
        precondition(Set(rules.map(\.name)).count == rules.count,
                     "Lexical rule names must be unique")
        self.rules = rules
    }

    public subscript(name: String) -> LexicalRuleDefinition? {
        rules.first { $0.name == name }
    }

    public var significantRules: [LexicalRuleDefinition] {
        rules.filter { $0.channel == .significant }
    }

    public var triviaRules: [LexicalRuleDefinition] {
        rules.filter { $0.channel == .trivia }
    }
}
