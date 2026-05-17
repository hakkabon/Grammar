//
//  GrammarBuilder.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/23.
//

import Foundation


@resultBuilder
public struct GrammarBuilder {
    
    public static func buildBlock(_ component: Production) -> Production {
        return component
    }

    public static func buildBlock(_ components: Production...) -> [Production] {
        return components
    }

    public static func buildBlock(_ components: [Production]...) -> [Production] {
        return components.flatMap { $0 }
    }
}

@resultBuilder
public enum ProductionBuilder {
    
    public static func buildBlock(_ component: ProductionResult) -> ProductionResult {
        return component
    }
}


@resultBuilder
public struct GrammarRuleBuilder {
    
    public static func buildBlock(_ component: Rule) -> Rule {
        return component
    }

    public static func buildBlock(_ components: Rule...) -> [Rule] {
        return components.map { $0 }
    }
}

/*
 The strategy:
 1. Elevate all plain symbols to Expression level
 2. Reduce all Expression into one single Expression by composing
    stuff with cat alt seq, etc.
 3. The implicit operator is concatenation => cat(Expression,Expression).
 */
@resultBuilder
struct RuleCatBuilder {

    static func buildBlock() -> Rule.Expression {
        .empty
    }
    static func buildExpression(_ expression: Symbol) -> Rule.Expression {
        .sym(expression)
    }

    static func buildExpression(_ expression: Cat) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Alt) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Seq) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Grp) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Opt) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Rule.Expression) -> Rule.Expression {
        expression
    }

    // Taking care of implicit concatenation first argument.
    static func buildPartialBlock(first: Rule.Expression) -> Rule.Expression  {
        first
    }

    // Taking care of implicit concatenation second argument.
    static func buildPartialBlock(accumulated: Rule.Expression, next: Rule.Expression) -> Rule.Expression {
        .cat(accumulated, next)
    }
}

/*
    The strategy:
    1. Elevate all plain symbols to Expression level
    2. Reduce all Expression into one single Expression by composing
    stuff with cat alt seq, etc.
    3. The implicit operator is alteration => alt(Expression,Expression).
 */
@resultBuilder
struct RuleAltBuilder {

    static func buildBlock() -> Rule.Expression {
        .empty
    }
    static func buildExpression(_ expression: Symbol) -> Rule.Expression {
        .sym(expression)
    }

    static func buildExpression(_ expression: Cat) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Alt) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Seq) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Grp) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Opt) -> Rule.Expression {
        expression.component
    }

    static func buildExpression(_ expression: Rule.Expression) -> Rule.Expression {
        expression
    }

    // Taking care of implicit concatenation first argument.
    static func buildPartialBlock(first: Rule.Expression) -> Rule.Expression  {
        first
    }

    // Taking care of implicit concatenation second argument.
    static func buildPartialBlock(accumulated: Rule.Expression, next: Rule.Expression) -> Rule.Expression {
        return .alt(accumulated, next)
    }
}
