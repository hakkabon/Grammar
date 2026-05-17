//
//  Counter.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2026/01/11.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

public class Counter {
    private static var count: Int = 0
    
    /// Increments the counter and returns the next value.
    public static func next() -> Int {
        // Swift static properties are thread-safe by default.
        count += 1
        return count
    }
    
    /// Optional: Resets the counter value.
    public static func reset() {
        count = 0
    }
}

