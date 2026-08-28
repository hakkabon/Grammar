//
//  GrammarLogger.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2025/09/21.
//  Copyright © 2025 hakkabon software. All rights reserved.
//

import Foundation

public enum GrammarLogLevel: String, Codable, Sendable {
    case trace
    case information
}

public enum GrammarLogCategory: String, Codable, Sendable {
    case grammar
    case parser
}

public struct GrammarLogEvent: Codable, Equatable, Sendable {
    public let level: GrammarLogLevel
    public let category: GrammarLogCategory
    public let message: String

    public init(level: GrammarLogLevel, category: GrammarLogCategory, message: String) {
        self.level = level
        self.category = category
        self.message = message
    }
}

public protocol GrammarLogSink: Sendable {
    func record(_ event: GrammarLogEvent)
}

public struct GrammarLogging: Sendable {
    private let recordEvent: @Sendable (GrammarLogEvent) -> Void

    public init<S: GrammarLogSink>(sink: S) {
        self.recordEvent = { event in sink.record(event) }
    }

    public init(record: @escaping @Sendable (GrammarLogEvent) -> Void) {
        self.recordEvent = record
    }

    public func record(_ event: GrammarLogEvent) {
        recordEvent(event)
    }

    public func trace(_ message: @autoclosure () -> String, category: GrammarLogCategory) {
        record(.init(level: .trace, category: category, message: message()))
    }

    public func information(_ message: @autoclosure () -> String, category: GrammarLogCategory) {
        record(.init(level: .information, category: category, message: message()))
    }

    public static let disabled = GrammarLogging { _ in }
}

#if canImport(OSLog)
import OSLog

public struct GrammarOSLogSink: GrammarLogSink {
    private let grammar = Logger(subsystem: "com.grammar.hakkabon", category: "Grammar")
    private let parser = Logger(subsystem: "com.grammar.hakkabon", category: "BNF-parser")

    public init() {}

    public func record(_ event: GrammarLogEvent) {
        let logger = event.category == .grammar ? grammar : parser
        switch event.level {
        case .trace:
            logger.trace("\(event.message, privacy: .public)")
        case .information:
            logger.info("\(event.message, privacy: .public)")
        }
    }
}

public extension GrammarLogging {
    static let osLog = GrammarLogging(sink: GrammarOSLogSink())
}
#endif
