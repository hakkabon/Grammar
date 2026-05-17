//
//  MetaTerminal.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/11/20.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

/// In formal language theory and compiler design, "Meta Terminals" (often called Special Terminals
/// or Boundary Markers) are symbols that don't represent actual characters in the input string but
/// provide critical structural information to the parser.
/// • Epsilon (ε or λ):
///   Represents an empty string. In a CFG, it allows a non-terminal to
///   "disappear" or derive nothing. It’s a mathematical convenience used to define optional
///   elements or nullable rules.
/// • EOF / End-of-File ($ or ⊥):
///   An artificial marker added to the end of the input stream. It tells the parser,
///   "The string is finished; if you are in a valid state, the parse is successful."
///   Without it, a parser might stop early or fail to realize the input is incomplete.

public enum MetaTerminal: String, Equatable, Hashable, CaseIterable, Codable {
    case eps = "ε"
    case lambda = "λ"
    case eof = "$"
    case eop = "¶"
    case empty = ""
}

extension MetaTerminal: CustomStringConvertible {
    public var description: String {
        switch self {
        case .empty: return "''"        // make the invisible visible
        default:
            return self.rawValue        // these are visible
        }
    }
}
