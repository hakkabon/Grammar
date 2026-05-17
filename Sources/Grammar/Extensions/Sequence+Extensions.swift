//
//  Sequence+Extensions.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/10/08.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

extension Sequence {
    @available(*, unavailable, renamed: "allSatisfy")
    public func allMatch(_ predicate: (Element) throws -> Bool) rethrows -> Bool {
        return try !self.contains(where: {try !predicate($0)})
    }
    
    public func unique<Property: Hashable>(by property: @escaping (Element) -> Property) -> AnySequence<Element> {
        return sequence(state: (makeIterator(), [])) { (state: inout (Iterator, Set<Property>)) -> Element? in
            while let next = state.0.next() {
                guard !state.1.contains(property(next)) else {
                    continue
                }
                state.1.insert(property(next))
                return next
            }
            return nil
        }.collect(AnySequence.init)
    }
}

extension Sequence {
    public func strided(_ stride: Int, start: Int? = nil) -> AnySequence<Element> {
        var iterator = self.makeIterator()
        iterator.skip(start ?? 0)
        return sequence(state: iterator) { (iterator: inout Iterator) -> Element? in
            let next = iterator.next()
            iterator.skip(stride - 1)
            return next
            }.collect(AnySequence.init)
    }
    
    // Improves code readability by transforming e.g. Set(a.map{...}.filter{...}) to a.map{...}.filter{...}.collect(Set.init)
    // so the order of reading equals the order of evaluation
    public func collect<Result>(_ collector: (Self) throws -> Result) rethrows -> Result {
        return try collector(self)
    }
    
    public func pairs() -> AnySequence<(Element, Element)> {
        return sequence(state: self.makeIterator()) { (iterator: inout Iterator) -> (Element, Element)? in
            guard let first = iterator.next(), let second = iterator.peek() else {
                return nil
            }
            return (first, second)
        }.collect(AnySequence.init)
    }

    public func prefixes() -> AnySequence<[Element]> {
        return sequence(state: (self.makeIterator(), [])) { (state: inout (Iterator, [Element])) -> [Element]? in
            guard let next = state.0.next() else {
                return nil
            }
            state.1.append(next)
            return state.1
        }.collect(AnySequence.init)
    }
}

extension Sequence where Element: Hashable {
    public func uniqueElements() -> AnySequence<Element> {
        return unique(by: {$0})
    }
}

extension Sequence where Element: Sequence {
    public func combinations() -> [[Element.Element]] {
        func combine(_ iterator: Iterator, partialResult: [[Element.Element]]) -> [[Element.Element]] {
            var iterator = iterator
            guard let next = iterator.next() else {
                return partialResult
            }
            return combine(iterator, partialResult: crossProduct(partialResult, next).map{$0 + [$1]})
        }
        return combine(makeIterator(), partialResult: [[]])
    }
}

extension Sequence {
    public func partition(_ isInFirstPartition: (Element) throws -> Bool) rethrows -> ([Element], [Element]){
        return try reduce(into: ([],[])) { (partitions: inout ([Element], [Element]), element: Element) in
            if try isInFirstPartition(element) {
                partitions.0.append(element)
            } else {
                partitions.1.append(element)
            }
        }
    }
}


fileprivate extension IteratorProtocol {
    mutating func skip(_ count: Int) {
        for _ in 0 ..< count {
            _ = self.next()
        }
    }
    
    func peek() -> Element? {
        var iterator = self
        return iterator.next()
    }
}

