//
//  Sequence.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2026/01/11.
//  Copyright © 2026 hakkabon software. All rights reserved.
//

import Foundation

extension Sequence {
    public func product<T: Sequence>(_ other: T) -> [(Element, T.Element)] {
        flatMap { x in
            other.map { y in
                (x, y)
            }
        }
    }
}

public func * <T: Sequence, U: Sequence>(lhs: T, rhs: U) -> [(T.Element, U.Element)] {
    lhs.flatMap { left in
        rhs.map { right in
            (left, right)
        }
    }
}

public func crossProduct<S1: Sequence, S2: Sequence>(_ lhs: S1, _ rhs: S2) -> AnySequence<(S1.Element, S2.Element)> {
    return sequence(
        state: (
            lhsIterator: lhs.makeIterator(),
            lhsElement: Optional<S1.Element>.none,
            rhsIterator: rhs.makeIterator(),
            rhsIteratorBase: rhs.makeIterator()
        ),
        next: { (state: inout (lhsIterator: S1.Iterator, lhsElement: S1.Element?, rhsIterator: S2.Iterator, rhsIteratorBase: S2.Iterator)) -> (S1.Element, S2.Element)? in
            guard let lhsElement = state.lhsElement ?? state.lhsIterator.next() else {
                return nil
            }
            state.lhsElement = lhsElement
            if let rhsElement = state.rhsIterator.next() {
                return (lhsElement, rhsElement)
            } else {
                state.rhsIterator = state.rhsIteratorBase
                
                guard let lhsNewElement = state.lhsIterator.next(), let rhsElement = state.rhsIterator.next() else {
                    return nil
                }
                state.lhsElement = lhsNewElement
                return (lhsNewElement, rhsElement)
            }
        }
    ).collect(AnySequence.init)
}

public func crossMap<S1: Sequence, S2: Sequence, ElementOfResult>(_ lhs: S1, _ rhs: S2, transform: (S1.Element, S2.Element) throws -> ElementOfResult) rethrows -> [ElementOfResult] {
    var result: [ElementOfResult] = Array()
    result.reserveCapacity(lhs.underestimatedCount * rhs.underestimatedCount)
    for e1 in lhs {
        for e2 in rhs {
            try result.append(transform(e1, e2))
        }
    }
    return result
}

public func crossFlatMap<S1: Sequence, S2: Sequence, ElementOfResult>(_ lhs: S1, _ rhs: S2, transform: (S1.Element, S2.Element) throws -> [ElementOfResult]) rethrows -> [ElementOfResult] {
    var result: [ElementOfResult] = Array()
    result.reserveCapacity(lhs.underestimatedCount * rhs.underestimatedCount)
    for e1 in lhs {
        for e2 in rhs {
            try result.append(contentsOf: transform(e1, e2))
        }
    }
    return result
}

public func unzip<A, B, SequenceType: Sequence>(_ sequence: SequenceType) -> (AnySequence<A>, AnySequence<B>) where SequenceType.Element == (A, B) {
    return (sequence.lazy.map{$0.0}.collect(AnySequence.init), sequence.lazy.map{$0.1}.collect(AnySequence.init))
}

public func unzip<A, B, SequenceType: Sequence>(_ sequence: SequenceType) -> ([A], [B]) where SequenceType.Element == (A, B) {
    return (sequence.map{$0.0}, sequence.map{$0.1})
}
