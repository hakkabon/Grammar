//
//  Character+Extensions.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/08/11.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

extension Character: Codable {
    public init(from decoder: Decoder) throws {
        let container = try decoder.singleValueContainer()
        let s = try container.decode(String.self)
        // if it's not a single character, use code FFFF to indicate illegal value
        self = s.count == 1 ? s.first! : "\u{FFFF}"
    }

    public func encode(to encoder: Encoder) throws {
        var container = encoder.singleValueContainer()
        try container.encode(String(describing: self))
    }
}
