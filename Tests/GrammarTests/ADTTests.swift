import Testing
@testable import Grammar

// MARK: - Stack tests

@Test func stack_pushAndPop() {
    var stack = Stack<Int>()
    stack.push(1)
    stack.push(2)
    stack.push(3)
    #expect(stack.pop() == 3)
    #expect(stack.pop() == 2)
    #expect(stack.pop() == 1)
    #expect(stack.pop() == nil)
}

@Test func stack_top_doesNotRemove() {
    var stack = Stack<Int>()
    stack.push(42)
    #expect(stack.top == 42)
    #expect(stack.top == 42)   // top is non-destructive
    #expect(stack.count == 1)
}

@Test func stack_isEmpty() {
    var stack = Stack<String>()
    #expect(stack.isEmpty == true)
    stack.push("x")
    #expect(stack.isEmpty == false)
    _ = stack.pop()
    #expect(stack.isEmpty == true)
}

@Test func stack_removeAll() {
    var stack: Stack<Int> = [1, 2, 3]
    stack.removeAll()
    #expect(stack.isEmpty == true)
}

@Test func stack_arrayLiteralInit() {
    let stack: Stack<Int> = [10, 20, 30]
    #expect(stack.count == 3)
}

// MARK: - Queue tests

@Test func queue_enqueueAndDequeue() {
    let queue = Queue<Int>()
    queue.enqueue(1)
    queue.enqueue(2)
    queue.enqueue(3)
    #expect(queue.dequeue() == 1)
    #expect(queue.dequeue() == 2)
    #expect(queue.dequeue() == 3)
}

@Test func queue_front_doesNotRemove() {
    let queue = Queue<String>()
    queue.enqueue("hello")
    #expect(queue.front == "hello")
    #expect(queue.front == "hello")
    #expect(queue.count == 1)
}

@Test func queue_isEmpty() {
    let queue = Queue<Int>()
    #expect(queue.isEmpty == true)
    queue.enqueue(5)
    #expect(queue.isEmpty == false)
    _ = queue.dequeue()
    #expect(queue.isEmpty == true)
}

@Test func queue_count() {
    let queue = Queue<Int>()
    #expect(queue.count == 0)
    queue.enqueue(1)
    queue.enqueue(2)
    #expect(queue.count == 2)
    _ = queue.dequeue()
    #expect(queue.count == 1)
}

@Test func queue_fifoOrdering() {
    let queue = Queue<Int>()
    for i in 1...5 { queue.enqueue(i) }
    var results: [Int] = []
    while !queue.isEmpty { results.append(queue.dequeue()) }
    #expect(results == [1, 2, 3, 4, 5])
}

@Test func queue_contains_equatable() {
    let queue = Queue<String>()
    queue.enqueue("a")
    queue.enqueue("b")
    queue.enqueue("c")
    #expect(queue.contains("b") == true)
    #expect(queue.contains("z") == false)
}
