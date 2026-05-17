import Foundation

protocol StackContainer {
    associatedtype Element
    
    mutating func push(_ element: Element)
    mutating func pop() -> Element?
    mutating func removeAll()
    var isEmpty: Bool { get }
    var top: Element? { get }
}

public struct Stack<T> : StackContainer {
    private var storage: [T] = []

    public mutating func push(_ element: T) {
        storage.append(element)
    }

    public mutating func pop() -> T? {
        storage.popLast()
    }

    public mutating func removeAll() {
        storage.removeAll()
    }

    public var isEmpty: Bool {
        storage.isEmpty
    }

    public var top: T? {
        storage.last
    }

    public var count: Int {
        storage.count
    }
}

extension Stack: ExpressibleByArrayLiteral {
    public init(arrayLiteral elements: T...) {
        self.storage = elements
    }
}

extension Stack: CustomStringConvertible, CustomDebugStringConvertible {
    public var description: String { return storage.description }
    public var debugDescription: String { return storage.debugDescription }
}

extension Stack {
    public func print() {
        storage.forEach() { Swift.print($0) }
    }
}
