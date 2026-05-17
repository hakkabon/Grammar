//
//  GrammarLogger.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2025/09/21.
//  Copyright © 2025 hakkabon software. All rights reserved.
//

import OSLog

extension Logger {
    /// Using your bundle identifier is a great way to ensure a unique identifier.
    private static var subsystem = "com.grammar.hakkabon"

    /// Logs all processing within the grammar domain.
    static let grammar = Logger(subsystem: subsystem, category: "Grammar")

    /// Logs all processing within the bnf domain.
    static let bnf = Logger(subsystem: subsystem, category: "BNF-parser")
}
