//
//  MetaSymbols.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2023/11/20.
//  Copyright © 2020 hakkabon software. All rights reserved.
//

import Foundation

/// A meta-symbol is a symbol used by EBNF to describe derivation rules.
/// Meta Symbols cannot appear in the productions when parsing. All parsing algorithms
/// used here operate on a grammar in the Standard Form, except for Meta Terminals.
/// Productions containing meta-symbols must therefore be resolved by rewriting these
/// production to Standard Form (BNF).
///
/// The symbols "{", "[", "(", "|", "}", "]", ")" are currently in use by the WSN and EBNF
/// grammar notations.

public enum MetaSymbol: String, Equatable, Hashable, CaseIterable, Codable {
    case lbrace = "{"
    case lbracket = "["
    case lparen = "("
    case rbrace = "}"
    case rbracket = "]"
    case rparen = ")"
    case alt = "|"
}

extension MetaSymbol: CustomStringConvertible {
    public var description: String {
        return self.rawValue
    }
}

let openMetaSymbols = Set([MetaSymbol.lbrace, MetaSymbol.lbracket, MetaSymbol.lparen])
let closeMetaSymbols = Set([MetaSymbol.rbrace, MetaSymbol.rbracket, MetaSymbol.rparen])
let parenSymbols = Set([MetaSymbol.lparen, MetaSymbol.rparen])
