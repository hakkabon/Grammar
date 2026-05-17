//
//  Either.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2026/01/11.
//  Copyright © 2026 hakkabon software. All rights reserved.
//

import Foundation

public enum Either<A, B> {
    case first(A)
    case second(B)
}

extension Either {
    public func map<ResultA, ResultB>(_ transformFirst: (A) throws -> ResultA, _ transformSecond: (B) throws -> ResultB) rethrows -> Either<ResultA, ResultB> {
        switch self {
        case .first(let a):
            return try .first(transformFirst(a))
            
        case .second(let b):
            return try .second(transformSecond(b))
        }
    }
    
    public func combine<Result>(_ transformFirst: (A) throws -> Result, _ transformSecond: (B) throws -> Result) rethrows -> Result {
        switch self {
        case .first(let a):
            return try transformFirst(a)
            
        case .second(let b):
            return try transformSecond(b)
        }
    }
}
