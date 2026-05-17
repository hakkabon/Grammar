//
//  ProductionBuilder.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/21.
//

import Foundation

protocol RuleRender {
    func render() -> String
}

public struct Rule {

    /// An `Expression` is nothing (empty), a single symbol, an empty symbol, or
    /// a composition of multiple expressions that are nested.
    public indirect enum Expression: CustomStringConvertible {
        public var description: String {
            switch self {
            case let .cat(a,b): return "\(a) , \(b)"
            case let .alt(a,b): return "\(a) | \(b)"
            case let .seq(expression): return "{ \(expression) }"
            case let .grp(expression): return "( \(expression) )"
            case let .opt(expression): return "[ \(expression) ]"
            case let .sym(symbol): return "\(symbol)"
            case .eps: return "ε"
            case .empty: return ""
            }
        }
        
        case cat(Expression,Expression)     // Cat concatenate operator
        case alt(Expression,Expression)     // ChoiceOf choice of operator
        case seq(Expression)                // ZeroOrMore repetition operator
        case grp(Expression)                // Group enclosing expression
        case opt(Expression)                // Optional enclosing expression
        case sym(Symbol)
        case eps
        case empty
    }

    /// Starting pattern
    public let goal: NonTerminal
    
    /// Symbols produced by substitution from the goal non terminal.
    public let rule: Expression

    public init(_ goal: NonTerminal, @RuleCatBuilder builder: () -> Expression) {
        self.goal = goal
        self.rule = builder()
    }
}

extension Rule: CustomStringConvertible {

    public var description: String {
    """
    \nRule(\(goal)} {
        \(rule)
    }
    """
    }
}

extension Rule: RuleRender {

    public func render() -> String {
        "\(goal) --> \(rule)"
    }
}

public struct Cat: RuleRender, CustomStringConvertible {
    let component: Rule.Expression
    public var description: String {
        "\(component)"
    }
    init(@RuleCatBuilder _ content: () -> Rule.Expression) {
        self.component = content()
    }
    func render() -> String {
        ""
    }
}

public struct Alt: RuleRender, CustomStringConvertible {
    let component: Rule.Expression
    public var description: String {
        "\(component)"
    }
    init(@RuleAltBuilder _ content: () -> Rule.Expression) {
        self.component = content()
    }
    func render() -> String {
        ""
    }
}

public struct Seq: RuleRender, CustomStringConvertible {
    let component: Rule.Expression
    public var description: String {
        "\(component)"
    }
    init(@RuleCatBuilder _ content: () -> Rule.Expression) {
        self.component = .seq(content())
    }
    func render() -> String {
        ""
    }
}

public struct Grp: RuleRender, CustomStringConvertible {
    let component: Rule.Expression
    public var description: String {
        "\(component)"
    }
    init(@RuleCatBuilder _ content: () -> Rule.Expression) {
        self.component = .grp(content())
    }
    func render() -> String {
        ""
    }
}

public struct Opt: RuleRender, CustomStringConvertible {
    let component: Rule.Expression
    public var description: String {
        "\(component)"
    }
    init(@RuleCatBuilder _ content: () -> Rule.Expression) {
        self.component = .opt(content())
    }
    func render() -> String {
        ""
    }
}


// Add the following
// • ZeroOrMore {}
// • OneOrMore {}
// • Optional {}
// • Subtract {}
