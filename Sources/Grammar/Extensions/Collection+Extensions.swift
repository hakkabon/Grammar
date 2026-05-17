//
//  Collection+Extensions.swift
//  grammar
//
//  Created by Ulf Akerstedt-Inoue on 2025/09/29.
//

import Foundation

extension Collection where Element: StringProtocol {
    public func longestCommonPrefix() -> String {
        guard let first = self.first.map({ String($0) }) else { return "" }
        return dropFirst().reduce(first, { $0.commonPrefix(with: $1) })
    }

    public func longestCommonSuffix() -> String {
        return String(self.lazy.map({ String($0.reversed()) }).longestCommonPrefix().reversed())
    }
}
