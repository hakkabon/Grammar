//
//  ProductionResult.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/09/21.
//  Copyright © 2023 hakkabon software. All rights reserved.
//

import Foundation

public enum ProductionResult {
    case con([Symbol])
    case alt([[Symbol]])
}

/// Custom Infix <+> Operator
infix operator <+> : ConcatenationPrecendence

/// Precedence and associativity definition of ConcatenationPrecendence Operator
precedencegroup ConcatenationPrecendence {
    associativity: left
    higherThan: AlternativePrecedence
    lowerThan: AdditionPrecedence
}

/// Custom Infix <|> Operator
infix operator <|> : AlternativePrecedence

/// Precedence and associativity definition of AlternativePrecedence Operator
precedencegroup AlternativePrecedence {
    associativity: left
    higherThan: ProductionPrecedence
}

/// Handle some implicit concatenation when using ( ... ) grouping of symbols
/// Concatenation of sets of strings
/// https://en.wikipedia.org/wiki/Concatenation
/// 1) (... con ...) <+> (... con ...)
/// 2) (... alt ...) <+> (... alt ...)
/// 3) (... con ...) <+> (... alt ...)
/// 4) (... alt ...) <+> (... con ...)
public func <+> (lhs: ProductionResult, rhs: ProductionResult) -> ProductionResult {
    switch (lhs,rhs) {
    case let (.con(lsymbols), .con(rsymbols)):
        let result = ProductionResult.con(lsymbols + rsymbols)
        return result
    case let (.alt(lsymbols), .alt(rsymbols)):
        let result = (lsymbols * rsymbols).compactMap( { $0.0 + $0.1 } )
        return ProductionResult.alt(result)
    case let (.con(lsymbols), .alt(rsymbols)):
        let result = ProductionResult.alt([lsymbols] + rsymbols)
        return result
    case let (.alt(lsymbols), .con(rsymbols)):
        let result = ProductionResult.alt(lsymbols + [rsymbols])
        return result
    }
}

public func <+> (lhs: ProductionResult, rhs: Symbol) -> ProductionResult {
    switch lhs {
    case let .con(symbols):
        return .con(symbols + [rhs])
    case let .alt(symbols):
        return .alt(symbols + [[rhs]])
    }
}

public func <+> (lhs: Symbol, rhs: ProductionResult) -> ProductionResult {
    switch rhs {
    case let .con(symbols):
        return .con([lhs] + symbols)
    case let .alt(symbols):
        return .alt([[lhs]] + symbols)
    }
}

public func <+> (lhs: Symbol, rhs: Symbol) -> ProductionResult {
    return .con([lhs, rhs])
}

public func <|> (lhs: ProductionResult, rhs: ProductionResult) -> ProductionResult {
    switch (lhs,rhs) {
    case let (.con(lsymbols), .con(rsymbols)):
        return .alt([lsymbols, rsymbols])
    case let (.alt(lsymbols), .alt(rsymbols)):
        return .alt(lsymbols + rsymbols)
    case let (.con(lsymbols), .alt(rsymbols)):
        return .alt([lsymbols] + rsymbols)
    case let (.alt(lsymbols), .con(rsymbols)):
        return .alt(lsymbols + [rsymbols])
    }
}

public func <|> (lhs: ProductionResult, rhs: Symbol) -> ProductionResult {
    switch lhs {
    case let .con(symbols):
        return .alt([symbols, [rhs]])
    case let .alt(symbols):
        return .alt(symbols + [[rhs]])
    }
}

public func <|> (lhs: Symbol, rhs: ProductionResult) -> ProductionResult {
    switch rhs {
    case let .con(symbols):
        return .alt([[lhs], symbols])
    case let .alt(symbols):
        return .alt([[lhs]] + symbols)
    }
}

public func <|> (lhs: Symbol, rhs: Symbol) -> ProductionResult {
    return .alt([[lhs], [rhs]])
}

/// Custom Infix --> Operator
infix operator --> : ProductionPrecedence

/// Precedence and associativity definition of ProductionPrecedence Operator
precedencegroup ProductionPrecedence {
    associativity: left
    lowerThan: AdditionPrecedence
}

/// Generates a production from a given non-terminal and produced sequence of symbols
///
/// - Parameters:
///   - lhs: Non-terminal pattern
///   - rhs: Produced string of symbols
/// - Returns: Production with the given pattern and generated result
public func --> (lhs: NonTerminal, rhs: ProductionResult) -> [Production] {
    switch rhs {
    case let .con(symbols):
        return [Production(goal: lhs, rule: symbols)]
    case let .alt(symbols):
        return symbols.map { rule in
            Production(goal: lhs, rule: rule)
        }
    }
}

/// Generates a production from the given non-terminal to the given symbol
///
/// - Parameters:
///   - lhs: Non-terminal pattern
///   - rhs: Produced symbol
/// - Returns: Production with the given pattern generating the given symbol
public func --> (lhs: NonTerminal, rhs: Symbol) -> Production {
    return Production(goal: lhs, rule: [rhs])
}
