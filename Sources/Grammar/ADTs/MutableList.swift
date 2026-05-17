
/// reference:
/// https://github.com/vinivendra/Gryphon/blob/release/Sources/GryphonLib/GryphonSwiftLibrary.swift#L228

import Foundation


public struct _ListSlice<Element>: Collection,
    BidirectionalCollection,
    RandomAccessCollection,
    MutableCollection
{
    public typealias Index = Int
    public typealias SubSequence = _ListSlice<Element>

    let list: List<Element>
    let range: Range<Int>

    public init(list: List<Element>, range: Range<Int>) {
        self.list = list
        self.range = range
    }

    public var startIndex: Int {
        return range.startIndex
    }

    public var endIndex: Int {
        return range.endIndex
    }

    public subscript(position: Int) -> Element {
        get {
            return list[position]
        }

        // For MutableCollection
        set {
            list._setElement(newValue, atIndex: position)
        }
    }

    public subscript(bounds: Range<Index>) -> _ListSlice<Element> {
        get {
            // From Collection.swift
            _failEarlyRangeCheck(bounds, bounds: startIndex..<endIndex)
            return _ListSlice(list: list, range: bounds)
        }

        // For MutableCollection
        set {
            for i in bounds {
                list._setElement(newValue[i], atIndex: i)
            }
        }
    }

    public func index(after i: Int) -> Int {
        return list.index(after: i)
    }

    // BidirectionalCollection
    public func index(before i: Int) -> Int {
        return list.index(before: i)
    }

    // RangeReplaceableCollection
    public init() {
        self.list = []
        self.range = 0..<0
    }

    // Other methods
    public func filter(_ isIncluded: (Element) throws -> Bool) rethrows -> List<Element> {
        let array = list.array[range]
        return try List(array.filter(isIncluded))
    }

    public func map<T>(_ transform: (Element) throws -> T) rethrows -> List<T> {
        let array = list.array[range]
        return try List<T>(array.map(transform))
    }

    public func compactMap<T>(_ transform: (Element) throws -> T?) rethrows -> List<T> {
        let array = list.array[range]
        return try List<T>(array.compactMap(transform))
    }

    public func flatMap<SegmentOfResult>(_ transform: (Element) throws -> SegmentOfResult) rethrows -> List<SegmentOfResult.Element> where SegmentOfResult: Sequence {
        let array = list.array[range]
        return try List<SegmentOfResult.Element>(array.flatMap(transform))
    }
}


public class List<Element>: CustomStringConvertible,
    CustomDebugStringConvertible,
    ExpressibleByArrayLiteral,
    Sequence,
    Collection
{
    public typealias Buffer = [Element]
    public typealias ArrayLiteralElement = Element
    public typealias Index = Int
    public typealias SubSequence = _ListSlice<Element>

    public var array: Buffer

    public init(_ array: Buffer) {
        self.array = array
    }

    // Custom (Debug) String Convertible
    public var description: String {
        return array.description
    }

    public var debugDescription: String {
        return array.debugDescription
    }

    // Expressible By Array Literal
    public required init(arrayLiteral elements: Element...) {
        self.array = elements
    }

    // Sequence
    public func makeIterator() -> IndexingIterator<List<Element>> {
        return IndexingIterator(_elements: self)
    }

    // Collection
    public var startIndex: Int {
        return array.startIndex
    }

    public var endIndex: Int {
        return array.endIndex
    }

    public subscript(position: Int) -> Element {
        return array[position]
    }

    public subscript(bounds: Range<Index>) -> _ListSlice<Element> {
        // From Collection.swift
        _failEarlyRangeCheck(bounds, bounds: startIndex..<endIndex)
        return _ListSlice(list: self, range: bounds)
    }

    public func index(after i: Int) -> Int {
        return array.index(after: i)
    }

    // BidirectionalCollection
    public func index(before i: Int) -> Int {
        return array.index(before: i)
    }

    // Used for _ListSlice to conform to MutableCollection
    fileprivate func _setElement(_ element: Element, atIndex index: Int) {
        array[index] = element
    }

    // Other methods
    public init<S>(_ sequence: S) where Element == S.Element, S: Sequence {
        self.array = Array(sequence)
    }

    public init() {
        self.array = []
    }

    /// Used to obtain a List with a new element type. If all elements in the list can be casted to
    /// the new type, the method succeeds and the new MutableList is returned. Otherwise, the method
    /// returns `nil`.
    public func `as`<CastedType>(_ type: List<CastedType>.Type) -> List<CastedType>? {
        if let castedList = self.array as? [CastedType] {
            return List<CastedType>(castedList)
        }
        else {
            return nil
        }
    }

    /// Used to obtain a List with a new element type. If all elements in the list can be casted to
    /// the new type, the method succeeds and the new MutableList is returned. Otherwise, the method
    /// crashes.
    public func forceCast<CastedType>(to type: List<CastedType>.Type) -> List<CastedType> {
        List<CastedType>(array as! [CastedType])
    }

    public func toList() -> List<Element> {
        return List(array)
    }

    public var isEmpty: Bool {
        return array.isEmpty
    }

    public var first: Element? {
        return array.first
    }

    public var last: Element? {
        return array.last
    }

    public func dropFirst(_ k: Int = 1) -> List<Element> {
        return List(array.dropFirst(k))
    }

    public func dropLast(_ k: Int = 1) -> List<Element> {
        return List(array.dropLast(k))
    }

    public func drop(while predicate: (Element) throws -> Bool) rethrows -> List<Element> {
        return try List(array.drop(while: predicate))
    }

    public func appending(_ newElement: Element) -> List<Element> {
        return List<Element>(self.array + [newElement])
    }

    public func filter(_ isIncluded: (Element) throws -> Bool) rethrows -> List<Element> {
        return try List(self.array.filter(isIncluded))
    }

    public func map<T>(_ transform: (Element) throws -> T) rethrows -> List<T> {
        return try List<T>(self.array.map(transform))
    }

    public func compactMap<T>(_ transform: (Element) throws -> T?) rethrows -> List<T> {
        return try List<T>(self.array.compactMap(transform))
    }

    public func flatMap<SegmentOfResult>(
        _ transform: (Element) throws -> SegmentOfResult)
        rethrows -> List<SegmentOfResult.Element>
        where SegmentOfResult: Sequence
    {
        return try List<SegmentOfResult.Element>(array.flatMap(transform))
    }

    public func prefix(while predicate: (Element) throws -> Bool) rethrows -> List<Element> {
        return try List<Element>(array.prefix(while: predicate))
    }

    @inlinable
    public func sorted(by areInIncreasingOrder: (Element, Element) throws -> Bool) rethrows -> List<Element> {
        return List(try array.sorted(by: areInIncreasingOrder))
    }

    public func appending<S>(contentsOf newElements: S) -> List<Element>
        where S: Sequence, Element == S.Element
    {
        return List<Element>(self.array + newElements)
    }

    public func reversed() -> List<Element> {
        return List(array.reversed())
    }

    public var indices: Range<Int> {
        return array.indices
    }
}



public class MutableList<Element>: List<Element>, MutableCollection {
    // MutableCollection
    public override subscript(position: Int) -> Element {
        get {
            return array[position]
        }
        set {
            array[position] = newValue
        }
    }

    public override subscript(bounds: Range<Index>) -> _ListSlice<Element> {
        get {
            // From Collection.swift
            _failEarlyRangeCheck(bounds, bounds: startIndex..<endIndex)
            return _ListSlice(list: self, range: bounds)
        }

        set {
            for i in bounds {
                array[i] = newValue[i]
            }
        }
    }

    // RangeReplaceableCollection
    override public required init() {
        super.init([])
    }

    public required init(arrayLiteral elements: Element...) {
        super.init(elements)
    }

    // Other methods
    public func append(_ newElement: Element) {
        array.append(newElement)
    }

    public func append<S>(contentsOf newElements: S) where S: Sequence, Element == S.Element {
        self.array.append(contentsOf: newElements)
    }

    public func insert(_ newElement: Element, at i: Index) {
        array.insert(newElement, at: i)
    }

    @discardableResult
    public func removeFirst() -> Element {
        return array.removeFirst()
    }

    @discardableResult
    public func removeLast() -> Element {
        return array.removeLast()
    }

    public func removeAll(keepingCapacity keepCapacity: Bool = false) {
        array.removeAll(keepingCapacity: keepCapacity)
    }

    @discardableResult
    public func remove(at index: Int) -> Element {
        return array.remove(at: index)
    }

    public func reverse() {
        self.array = self.array.reversed()
    }

    override public func drop(while predicate: (Element) throws -> Bool) rethrows -> List<Element> {
        return try List(array.drop(while: predicate))
    }
}
