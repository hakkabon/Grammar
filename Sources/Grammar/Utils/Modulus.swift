//
//  Modulus.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2026/01/11.
//  Copyright © 2026 hakkabon software. All rights reserved.
//

import Foundation

/// Calculates a mod b where b can be a negative number.
/// - Parameters:
///   - a: First number
///   - b: Second number
/// - Returns: Calculated  modulus
///
public func mod(_ a: Int, with b: Int) -> Int {
    if b < 0 {
        return mod(-a, with: -b)
    }
    var ret: Int = a % b
    if ret < 0 {
        ret += b
    }
    return ret
}
