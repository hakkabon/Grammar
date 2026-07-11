//
//  StandardNotation.swift
//  Grammar
//
//  Created by Ulf Akerstedt-Inoue on 2026/01/02.
//  Copyright © 2026 hakkabon software. All rights reserved.
//

import Foundation

public struct StandardNotation {
    
    public init() {}
    
    /// Converts an EBNF syntax tree into a flat list of BNF Productions using plain
    /// BNF notation. The syntax tree looks somthing like the following:
    /// ```
    /// Syntax Root
    ///    ├── Regex <id> : /[a-zA-Z][a-zA-Z0-9-_]*/
    ///    ├── Regex <id> : /[\d]+/
    ///    ├── Range <id> : \u{0400}..\u{04FF}
    ///    ├── List <id> : ["\\u{1F600}", "\\u{1F602}"]
    ///    ├── Start <non-terminal>
    ///    ├── Empty ε
    ///    ├── Production: <non-terminal>
    ///    │   └── Alternative
    ///    │       ├── <rule>
    ///    │       └── Sequence
    ///    │           ├── <rule>
    ///    │           └── <syntax>
    ///    ├── Production: ...
    ///```
    /// - Returns: all productions reduced to BNF and all newly generated non-terminals.
    public func rewriteToStandardNotation(syntax: BnfExpression) -> ([Production], Set<NonTerminal>, start: String, empty: String, lexical: [String: Terminal]) {
        var productions: [Production] = []
        var nonTerminals = Set<NonTerminal>()           // generated non-terminals
        var start: String = ""                          // generic grammar only
        var empty: String = "ε"                         // generic grammar only
        var tokens: [String: Terminal] = [:]
        
        func addProduction(goal: NonTerminal, rule: [Symbol]) {
            let prod = Production(goal: goal, rule: rule)
            productions.append(prod)
        }

        /// Returns a new unique nonterminal, based on the given set of non-terminals,
        /// based on the given suggestion.
        /// Note: '@' denotes internal/synthetic
        func generateNonterminal(withPrefix prefix: String, nonTerminals: Set<NonTerminal>) -> NonTerminal {
            var symbol = "@\(prefix)_\(Counter.next())"
            while nonTerminals.contains(NonTerminal(name: symbol)) {
                symbol = "@\(prefix)_\(Counter.next())"
            }
            return NonTerminal(name: symbol)
        }

        /// Converts an EBNF expression into a linear list of Symbols.
        /// If nested structures (groups, curly braces) are found, it generates
        /// synthetic productions as side effects and returns the new NonTerminal symbol.
        func processRule(_ expression: BnfExpression) -> [Symbol] {
            
            switch expression {
                
            case .terminal(let value):
                guard let meta = MetaTerminal(rawValue: value) else {
                    // The string did not match any of the meta terminal strings,
                    // therefore it must be an ordinaly terminal.
                    return [.terminal(.string(string: value))]
                }
                return [.terminal(.meta(meta))]
                
            case .nonterminal(let value):
                // A reference like `<Identifier>` inside an ordinary production is
                // ambiguous on its own: it looks exactly like a reference to another
                // production. If `value` is the identifier of a `lexical { }`
                // declaration (regex, range, or list), it isn't a non-terminal at
                // all — it names a Terminal. Resolving it here means every lexical
                // definition is automatically usable wherever it's referenced,
                // with no separate wiring required downstream by any parser: this
                // becomes a plain `Symbol.terminal(...)`, exactly like a literal
                // `"+"` or `<Identifier>` would already be if it were a hand-written
                // `.terminal` case. `tokens` must already be fully populated by the
                // time this runs — see the two-pass structure below.
                if let terminal = tokens[value] {
                    return [.terminal(terminal)]
                }
                return [.nonTerminal(NonTerminal(name: value))]
                
            case .empty:
                // Epsilon is represented internally as the empty rule `[]`, never as an
                // explicit symbol; `Production.init` would normalize it away regardless,
                // but writing `[]` directly here keeps the intent unambiguous. The
                // configured meta character ('ε' by default) is applied only when the
                // grammar is rendered for display.
                return []
                
            case .sequence(let items):
                return items.flatMap { processRule($0) }
                
            // Nested Alternative ( Grouping inside a rule )
            // Rule: A -> B (C | D) E
            // Action: Create Aux. Aux -> C, Aux -> D. Return [B, Aux, E]
            case .alternative(let items):
                let auxGoal = generateNonterminal(withPrefix: "alt", nonTerminals: nonTerminals)
                nonTerminals.insert(auxGoal)
                
                for item in items {
                    let symbols = processRule(item)
                    addProduction(goal: auxGoal, rule: symbols)
                }
                return [.nonTerminal(auxGoal)]
                
            // Optional [ ... ]
            // Rule: A -> [B]
            // Action: Create Aux. Aux -> B, Aux -> ε. Return [Aux]
            case .optional(let expr):
                let auxGoal = generateNonterminal(withPrefix: "opt", nonTerminals: nonTerminals)
                nonTerminals.insert(auxGoal)

                // Path 1: The expression exists
                let contentSymbols = processRule(expr)
                addProduction(goal: auxGoal, rule: contentSymbols)
                
                // Path 2: Epsilon (it was skipped) — represented as the empty rule.
                addProduction(goal: auxGoal, rule: [])
                
                return [.nonTerminal(auxGoal)]
                
            // Repetition { ... } (Zero or more)
            // Rule: A -> {B}
            // Action: Create Aux. Aux -> B Aux, Aux -> ε. Return [Aux]
            // (Right-recursive definition)
            case .repetition(let expr):
                let auxGoal = generateNonterminal(withPrefix: "rep", nonTerminals: nonTerminals)
                nonTerminals.insert(auxGoal)

                // Path 1: Match content, then recurse
                var contentSymbols = processRule(expr)
                contentSymbols.append(.nonTerminal(auxGoal)) // Add self at end
                addProduction(goal: auxGoal, rule: contentSymbols)
                
                // Path 2: Epsilon (end of loop) — represented as the empty rule.
                addProduction(goal: auxGoal, rule: [])
                
                return [.nonTerminal(auxGoal)]
                
            // Repetition One Plus { ... }+
            // Rule: A -> {B}+
            // Action: Create Aux. Aux -> B, Aux -> B Aux. Return [Aux]
            case .repetitionOnePlus(let expr):
                let auxGoal = generateNonterminal(withPrefix: "rep1", nonTerminals: nonTerminals)
                nonTerminals.insert(auxGoal)
                let contentSymbols = processRule(expr)
                
                // Path 1: Just B (base case)
                addProduction(goal: auxGoal, rule: contentSymbols)
                
                // Path 2: B then recurse
                var recursiveSymbols = contentSymbols
                recursiveSymbols.append(.nonTerminal(auxGoal))
                addProduction(goal: auxGoal, rule: recursiveSymbols)
                
                return [.nonTerminal(auxGoal)]
                
            // Grouping ( ... )
            // Usually handles simple precedence, treated like nested sequence or alternative
            case .grouping(let expr):
                // If the group contains an alternative, the alternative case handles the creation of a new NT.
                // If it's just a sequence, we flatten it.
                // However, to be safe and preserve structure, we usually treat ( ) as a sub-rule.
                
                // Check optimization: if expr is just a sequence, flatten it directly without new rule
                if case .sequence = expr {
                    return processRule(expr)
                }
                // If it's an alternative or complex, delegating to processRHS might recurse back
                // to .alternative which creates the NT.
                return processRule(expr)
                
            default:
                print("Warning: Unhandled EBNF construct \(expression)")
                return []
            }
        }
        
        // If the root is .syntax, process all children.
        if case .syntax(let expressions) = syntax {

            // Pass 1: collect every lexical definition (regex, range, list) into
            // `tokens` *before* any production is rewritten. A `lexical { }` block
            // may appear anywhere in the source file relative to the productions
            // that reference its identifiers — collecting them up front, in a
            // dedicated pass, means `processRule`'s `.nonterminal` case (which
            // consults `tokens`) always sees the complete set, regardless of
            // declaration order in the source grammar.
            for expression in expressions {
                switch expression {
                case .regex(let identifier, let pattern):
                    if let terminal = try? Terminal(expression: pattern) {
                        tokens[identifier] = terminal
                    } else {
                        print("Warning: invalid regular expression for lexical definition '\(identifier)': /\(pattern)/")
                    }

                case .range(let identifier, let lower, let upper):
                    if let lowerChar = lower.first, lower.count == 1,
                       let upperChar = upper.first, upper.count == 1,
                       lowerChar <= upperChar {
                        tokens[identifier] = Terminal(range: lowerChar ... upperChar)
                    } else {
                        print("Warning: invalid range definition '\(identifier)': '\(lower)' .. '\(upper)'")
                    }

                case .list(let identifier, let elements):
                    tokens[identifier] = Terminal(list: elements)

                default:
                    break
                }
            }

            // Pass 2: rewrite productions, `start`, and `empty`. `tokens` is now
            // complete, so any `<identifier>` reference resolved inside `processRule`
            // that names a lexical definition is substituted with its `Terminal`
            // automatically, wherever in the grammar it's used.
            for expression in expressions {
                if case .production(let goal, let body) = expression {
                    let goal = NonTerminal(name: goal)

                    // A production goal that shares its name with a lexical
                    // definition is ambiguous authoring (which one wins when the
                    // name is referenced elsewhere?) rather than something to
                    // silently resolve one way or the other.
                    if tokens[goal.name] != nil {
                        print("Warning: '\(goal.name)' is defined both as a production and as a lexical identifier; the lexical definition takes precedence wherever '\(goal.name)' is referenced.")
                    }

                    // If the body is an alternative (A | B), we generate multiple productions for the same goal.
                    // Goal -> A
                    // Goal -> B
                    if case .alternative(let options) = body {
                        for option in options {
                            let symbols = processRule(option)
                            addProduction(goal: goal, rule: symbols)
                        }
                    } else {
                        // Otherwise, it's a single rule
                        let symbols = processRule(body)
                        addProduction(goal: goal, rule: symbols)
                    }
                }
                else if case .start(let symbol) = expression {
                    start = symbol
                }
                else if case .empty(let symbol) = expression {
                    empty = symbol
                }
            }
        } else {
            print("syntax tree is malformed - call the police immediately!")
        }
        
        return (productions, nonTerminals, start, empty, tokens)
    }
}
