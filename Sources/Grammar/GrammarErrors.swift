//
//  GrammarErrors.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2020/05/23.
//

import Foundation

@available(OSX 10.12, iOS 10.0, watchOS 3.0, tvOS 10.0, *)
public extension Grammar {
    enum GrammarError: Swift.Error {
        case unrecognizedPunctuation(String)
        case unexpectedEOF
    }
}
