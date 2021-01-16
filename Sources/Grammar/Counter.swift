//
//  Counter.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2020/05/20.
//

import Foundation

public class Counter {
    private (set) var value: Int = 0

    public init() {}
    
    public func increment() -> Int {
        DispatchQueue.global().sync {
            value += 1
        }
        return value
    }
}
