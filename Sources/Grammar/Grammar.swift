//
//  Grammar.swift
//  Grammar
//
//  Created by Ulf Inoue on 1/7/15.
//  Copyright (c) 2015 HakkaBon. All rights reserved.
//
import Foundation
import Files
import BNF

/// A class representing a context-free grammar (CFG) as defined by
/// G = (V, T, P, S), where
///   V is the set of nonterminals,
///   T is the set of terminals,
///   P a set of production rules, in the form P: N → (N ∪ T)*
///   S is the start symbol of the grammar.
///
/// References
/// ----------
/// [1] Modern Compiler Design, 2nd Edition
///     Grune, Dick and Reeuwijk, Kees van and Bal, Henri E. and Jacobs, Ceriel J.H. and Langendoen, Koen
///     Springer Publishing Company 2012
/// [2] Compilers: Principles, Techniques, and Tools, 2nd Edition
///     by Alfred V. Aho, Ravi Sethi, and Jeffrey D. Ullman
///     Addison Wesley 2007
/// [3] Crafting a compiler
///     by Charles N., Cytron, Ron K., LeBlanc Jr., Richard J Fischer
///     Pearson 2009

public class Grammar {
    
    enum Symbol: String, CaseIterable {
        case comment = "//"
        case commentOpen = "/*"
        case commentClose = "*\\"
        case colon = ":"
        case comma = ","
        case derives = "->"
        case dot = "."
        case dquote = "\""
        case greater = ">"
        case lbrace = "{"
        case lbracket = "["
        case lcode = "{:"
        case less = "<"
        case lparen = "("
        case not = "!"
        case mul = "*"
        case or = "|"
        case plus = "+"
        case squote = "'"
        case rbrace = "}"
        case rbracket = "]"
        case rcode = ":}"
        case rparen = ")"
        case semicolon = ";"
    }
    
    public struct Constant {
        // The augmented start symbol.
        public static let start = "$"
        
        // Epsilon character ε, for nullable derivations.
        public static let eps = "ε"
        
        // EOF symbol '¶'.
        public static let eof = "¶"
    }

    // Definitions of allowed BNF meta symbols.
    enum MetaSymbol { case grouping, option, repetition, alternation }
    
    // [α=ε β≠ε], [α≠ε β≠ε], [α≠ε β=ε] in A → α N β
    // same for γ and δ in B → γ{X1...Xm}δ
    enum Slice { case low, middle, high, complete }

    // Translation table for EBNF meta punctuation.
    let translate: [String:String] = [
        "[" : ".[.",
        "]" : ".].",
        "{" : ".{.",
        "}" : ".}.",
        "(" : ".(.",
        ")" : ".).",
        "|" : ".|.",
    ]
    
    // Lookup table for EBNF meta punctuation.
    let reverse: [Symbol:String] = [
        Symbol.lbracket : ".[.",
        Symbol.rbracket : ".].",
        Symbol.lbrace : ".{.",
        Symbol.rbrace : ".}.",
        Symbol.lparen : ".(.",
        Symbol.rparen : ".).",
        Symbol.or : ".|.",
    ]
    
    // Collection of all productions in the grammar.
    public var productions: [ProductionRule] = [ProductionRule]()
    
    // Map associating nonterminals with its production(s).
    public var itsProductions: [String:[ProductionRule]] = [:]
    
    // Collection of all nonterminals in the grammar.
    public var nonterminals: Set<String> = Set<String>()
    
    // Collection of all terminals in the grammar.
    public var terminals: Set<String> = Set<String>()

    // Collection of token definitions (regular expressions in grammar)
    var tokens: [String:String] = [String:String]()

    // Collection of nonterminals that derives to empty strings (epsilon)
    public var symbolDerivesEmpty: [String:Bool] = [:]
    
    // Sets of first symbols
    public var firstSets: [String:Set<String>] = [:]

    // sets of follow symbols
    public var followSets: [String:Set<String>] = [:]

    // Counter that produces a unique priority number for each `Production`.
    static var priority: Counter = Counter()

    // Counter that produces unique ids for ENBF re-writing rules.
    public var counter: Counter = Counter()

    // Collection of all meta-terminals (EBNF symbols).
    public var metaterminals: Set<String> = [ "[" , "]", "{", "}", "(" , ")", "|" ]
    public let numerals: Set<String> = [ "0" , "1", "2", "3", "4" , "5", "6", "7", "8", "9" ]
    public let punctuation: Set<String> = [ "+" , "-", "*", "/", "=" ]

    // Name of the grammar.
    public private(set) var name: String = ""

    // The start (goal = the very first nonterminal) symbol of this Grammar.
    public var S = ""

    // Not meant to be used.
    private init() { }

    /// Create grammar from given text file.
    /// - Parameters
    ///   - file: text file (ascii) containing the complete grammar description of the language.
    /// - Parameter level: optionally define debug trace for the BNF parser.
    /// - Throws: if failed to open file.
    public init(grammar file: File, level: Parser.TraceOptions = []) throws {
        let parser = try Parser(grammar: file, level: level)
        initialize(parser: parser)
    }
    
    /// Create grammar from given multiline string.
    /// - Parameter source: String containing complete grammar description of the language.
    /// - Parameter level: optionally define debug trace for the BNF parser.
    public init(grammar source: String, level: Parser.TraceOptions = []) {
        precondition(source.count > 0, "Must define an input grammar.")
        let parser = Parser(grammar: source, level: level)
        initialize(parser: parser)
    }

    /// Create grammar from given production rules.
    /// Grammar snippets adhear to the the convention:
    ///     Upper case symbols are nonterminals, lower case symbols are terminals.
    /// - Parameter rules: All production rules describing the language.
    public init(grammar name: String, productions rules: [ProductionRule]) {
        precondition(rules.count > 0, "Must have at least one production rule defined.")

        self.name = name
        self.productions = rules
                    
        // Do split productions at '|' character.
        for p in rules {
            let goal = p.lhs
            let parts = p.rhs.filter({ $0 == "|" })
            for part in parts {
                productions.append(ProductionRule(lhs:goal, rhs:[part]))
            }
        }
    
        for p in productions {
            nonterminals.insert(p.lhs)
            for symbol in p.rhs {
                if metaterminals.contains(symbol) {}
                else if symbol == Constant.start { nonterminals.insert(symbol) }
                else if symbol == Constant.eps { metaterminals.insert(symbol) }
                else if !terminal(symbol: symbol) && symbol == symbol.uppercased() { nonterminals.insert(symbol) }
                else if terminal(symbol: symbol) { terminals.insert(symbol) }
            }
            if itsProductions[p.lhs] != nil {
                itsProductions[p.lhs]!.append(p)
            } else {
                itsProductions[p.lhs] = [p]
            }
        }

        // Assign lhs of first production as start symbol.
        if S.count == 0 { S = productions[0].lhs }

        initialize(parser: nil)
    }

    /// Common initializer.
    func initialize(parser: Parser?) {
        
        func newProduction(lhs: String, rhs: [String], semantic action: [String]) {
            if lhs.count > 0 && rhs.count > 0 {
                let production = createProduction(lhs: lhs, phrase: rhs)
                if action.count > 0 { production.semanticAction = action }
            }
        }
        
        if let parser = parser {
            var lhs: String = ""
            var rhs: [String] = []
            var action: [String] = []

            parser.traverse { (ast) in
                switch ast.node {
                case .root: break
                case let .grammar(identifier): self.name = identifier
                case let .token(identifier,value): collectTokens(identifier: identifier, regex: value)
                case .production(_):
                    newProduction(lhs: lhs, rhs: rhs, semantic: action)
                    lhs = ""; rhs = []; action = []
                case let .lhs(identifier):
                    lhs = identifier
                    nonterminals.insert(identifier)
                    // Assign lhs of first production as start symbol.
                    if S.count == 0 { S = lhs }
                case let .terminal(symbol):
                    rhs.append(symbol)
                    terminals.insert(symbol)
                case let .nonterminal(identifier):
                    rhs.append(identifier)
                    nonterminals.insert(identifier)
                case let .semanticAction(string):
                    action.append(string)
                case let .punctuation(symbol):
                    // These tokens are EBNF/BNF punctuation and must be codified.
                    if let encoded = translate[symbol] {
                        rhs.append(encoded)
                    } else {
                        fatalError()
                    }
                }
            }
            newProduction(lhs: lhs, rhs: rhs, semantic: action)
        }

        // Augment grammar with new goal symbol.
        augment(grammar: Constant.start)
        
        // Remove any meta characters from nonterminal sets.
        cleanNonterminalSet()

        // Do a sanity check - do not proceed if there are issues at this stage.
        guard sanityCheck() else { return }

        // Transform grammar from EBNF to CFG Standard Form in four steps.
        rewriteGroupings()
        rewriteOptions()
        rewriteRepetitions()
        rewriteAlternations()

        guard cleanGrammar() else { return }

        // Do consistency check of grammar.
        consistencyCheck()
        
        // Derive all empty productions of grammar.
        emptyDerivationCheck()
        
        // Calculate FIRST/FOLLOW sets for all nonterminal symbols.
        firstSet()
        followSet()
    }
   
    /// Creates one production of the form nonterminal -> phrase, where first
    /// symbol designates the non terminal following an array of symbols which
    /// equals the phrase, for example "E", ["T", "|", "E"].
    /// - Parameters:
    ///   - nonterminal: symbol used as goal of dervation (substitution).
    ///   - phrase: collection of symbols including EBNF designating rule for dervation (substitution).
    /// Returns:
    ///    One new production of the form nonterminal -> phrase.
    func createProduction(lhs nonterminal: String, phrase: [String]) -> ProductionRule {
        let p = ProductionRule(lhs: nonterminal, rhs: phrase)     // production has to be a class, otherwise
        productions.append(p)                                      // we get a copy put into lookup array
        if let i = itsProductions.index(forKey: nonterminal) {
            if !itsProductions.values[i].contains(p) {
                itsProductions.values[i].append(p)
            }
        } else {
            itsProductions[nonterminal] = [p]
        }
        return p
    }
    
    /// Collect all token definitions (regular expressions).
    private func collectTokens(identifier: String, regex: String) {
        tokens[identifier] = regex
    }
    
    /// Grammar *snippets* adhear to the the convention:
    /// Upper case symbols are nonterminals, lower case symbols are terminals.
    /// - Parameter symbol: symbol to be investigated
    /// - Returns: true if symbol is a terminal, otherwise false.
    func terminal(symbol: String) -> Bool {
        return numerals.contains(symbol) || punctuation.contains(symbol) || symbol == symbol.lowercased()
    }

    public func isNonterminal(symbol: String) -> Bool {
        return nonterminals.contains(symbol)
    }
    
    public func isTerminal(symbol: String) -> Bool {
        return terminals.contains(symbol)
    }

    /// Augment grammar with new start symbol
    /// - Parameter start: start symbol
    public func augment(grammar start: String) {
        // check if grammar is augmented or not
        guard !nonterminals.contains(start) else { return }
        
        // add new start symbol and new production: start -> S
        let startRule = ProductionRule(lhs: start, rhs: [S])
        productions.append(startRule)
        
        // set new start symbol
        S = start
        nonterminals.insert(start)
        itsProductions[start] = [startRule]
    }

    // Compute the set of nullable nonterminals: { A in V | A =>* eps }
    // I decided to go with a simple fixed-point algorithm
    public func closure() -> Set<String> {
        var nullSet = Set<String>()
        for p in productions {
            if p.rhs[0] == Constant.eps { nullSet.insert(p.lhs) }
        }
        if nullSet.count != 0 {
            var isNullable = true
            var size:Int = nullSet.count
            repeat {
                size = nullSet.count
                for p in productions {
                    isNullable = true
                    for s in p.rhs {
                        if s == s.lowercased() || !nullSet.contains(s) {
                            isNullable = false
                            break
                        }
                    }
                    if isNullable {
                        nullSet.insert(p.lhs)
                    }
                }
            } while (size != nullSet.count)
        }
        return nullSet
    }

    /// Returns true if this grammar is LL(1), otherwise false.
    public var isLL1: Bool {
        for A in nonterminals {
            var set = Set<String>()
            for p in itsProductions[A]! {
                var predict = first(symbol: p.rhs)
                if predict.contains(Constant.eps) {
                    predict.formUnion(followSets[A]!)
                }
                if set.intersection(predict).isEmpty { return false }
                set.formUnion(predict)
            }
        }
        return true
    }
}

// Print Protocol conformance

extension Grammar: CustomStringConvertible {
    public var description: String {
        var s = "Grammar:\n"
        for p in productions { s += "\(p)\n" }
        return s
    }
}

extension Grammar {
    
    public enum OutputLevel { case basic, full }

    public func printGrammar(detail: OutputLevel = .basic) {
        switch detail {
        case .basic:
            printBasicReport()
        case .full:
            printFullReport()
        }
    }
    
    func printBasicReport() {
        for A in nonterminals {
            for p in itsProductions[A]! {
                print("\t\(p)")
            }
        }
        print("Start (goal) terminal: \(S)")
        print("All Terminals \(terminals.count):")
        for t in terminals { print("\t\(t)") }
        
        print("All Nonterminals \(nonterminals.count):")
        for nt in nonterminals {
            print("\t\(nt)")
        }
    }
    
    func printFullReport() {
        print("\nGrammar '\(name)' definition:")

        print("Lexical definitions:")
        for t in tokens.keys {
            print("\t\(t) : \(tokens[t]!)")
        }
        print("Start (goal) terminal: \(S)")
        print("All Terminals \(terminals.count):")
        for t in terminals { print("\t\(t)") }
        
        print("All Nonterminals \(nonterminals.count):")
        for nt in nonterminals {
            print("\t\(nt)")
        }
                
        print("All Productions \(productions.count):")
        for key in itsProductions.keys {
            for p in itsProductions[key]! {
                print("\t\(p)")
            }
        }

        print("Productions with empty derivation:")
        for p in productions {
            if p.derivesEmpty {
                print("\t\(p)")
            }
        }

        print("Nullable nonterminals: { \(closure().joined(separator: ", ")) } ")

        print("FIRST SET")
        for nt in nonterminals {
            print("\t\(nt) = \( first(symbol: [nt]) )")
        }
        
        print("FOLLOW SET")
        for symbol in nonterminals {
            print("\t \(symbol)  = \( String(describing: followSets[symbol]) )")
        }
        
        let s = isLL1 ? "is LL(1) parseble" : "is not LL(1) parseble"
        print("\nGrammar '\(name)' \(s)")
    }
}




//MARK: Grammar Checks

extension Grammar {

    // [1] Modern Compiler Design, gives a few pointers in chapter
    // 2.9 Hygiene in Context-Free Grammars.
    //
    // Also at Wikipedia:
    // https://en.wikipedia.org/wiki/Context-free_grammar#cite_note-20

    /// Meta charactrs like 'ε' are allowed to appear in grammar definition, but
    /// they are not considered to be real nonterminals and have therefore to be
    /// removed form the set of nonterminal characters.
    private func cleanNonterminalSet() {
        nonterminals.remove(Constant.eps)
    }

    /// Chck that all encoded EBNF [,],{,},(,),|  are removed form the set grammar.
    private func cleanGrammar() -> Bool {
        let metaCharacters = Set<String>(translate.values)
        var result = nonterminals.allSatisfy { !metaCharacters.contains($0) }
        result = result || terminals.allSatisfy { !metaCharacters.contains($0) }
        for A in nonterminals {
            for p in itsProductions[A]! {
                result = result || p.rhs.allSatisfy { !metaCharacters.contains($0) }
            }
        }
        return result
    }

    /// Runs a sanity check on the given grammar.
    /// - Detect any lexical definitions in any of the production rules.
    /// - Verify that all token ids are infact defined terminal symbols
    /// There is no meaning in proceeding to further analysis if there are
    /// issues at this stage.
    func sanityCheck() -> Bool {
        var ok = true

        // Check for lexical definitions in the productions.
        for p in productions {
            if terminals.contains( p.lhs ) {
                print("production head '\(p.lhs)' in production '\(p)' is a lexical definition.")
                ok = false
            }
        }
        if !ok { return ok }

        // Verify that all token ids are infact defined terminal symbols
        for t in tokens.keys {
            if !terminals.contains(t) {
                print("token identifier '\(t)' is not defined as a terminal symbol.")
                ok = false
            }
        }
        if !ok { return ok }

        // Verify that all nonterminals have production rules defined.
        for A in nonterminals {
            if itsProductions[A] == nil {
                print("non terminal '\(A)' does not have any production rules defined.")
                ok = false
            }
        }
        if !ok { return ok }

        return ok
    }

    /// Rules in a context-free grammar can be useless through three causes:
    /// 1) they may contain undefined non-terminals,
    /// 2) they may fail to produce anything,
    /// 3) and they may not be reachable from the start symbol.
    func consistencyCheck() {
        undefinedNonterminalsCheck()
        unproductiveRuleCheck()
        unreachableNonterminalCheck()
    }
    
    /// Searches grammar for nonterminals without any production rule.
    func undefinedNonterminalsCheck() {

        // check undefined Nonterminals
        for nt in nonterminals {
            if itsProductions[nt] == nil {
                print("nonterminal '\(nt)' does not have a production rule.")
            }
        }
    }

    /// A rule is productive if its right-hand side consists of symbols all of
    /// which are productive. Terminal symbols are productive since they produce
    /// terminals and empty is productive since it produces the empty string. A
    /// non-terminal is productive if there is a productive rule for it.
    /// Iterate over all productions until set of 'productive symbols' does not
    /// grow anymore. Production A → α B β is non-productive as long as one
    /// nonterminal is non-productive.
    func unproductiveRuleCheck() {
        // marks productive grammar rules as true
        var productiveRule: [ProductionRule:Bool] = [:]
        
        // marks productive grammar nonterminals as true
        var productiveSymbol: [String:Bool] = [:]
        
        // initialize all productions in the grammar to non-productive
        for p in productions { productiveRule[p] = false }
        
        // initialize all nonterminals in the grammar to non-productive
        for nt in nonterminals { productiveSymbol[nt] = false }
        
        // loop until set of productive symbols does not grow anymore
        var n: Int = 0
        var m: Int = 0
        repeat {
            n = m
            for p in productions {
                var productive = true
                for s in p.rhs {
                    // all terminals are productive A → a including A → ε
                    if isTerminal(symbol: s) || s == Constant.eps { continue }
                    // production A → α B β is non-productive as long as one
                    // nonterminal is non-productive, here B=s
                    if isNonterminal(symbol: s) {
                        if !productiveSymbol[s]! { productive = false }
                    }
                }
                productiveRule[p] = productive
            }
            
            // collect any new productive nonterminals
            for p in productions {
                if productiveRule[p]! { productiveSymbol[p.lhs] = true }
            }
            // calculate current cardinality of productive symbols set
            m = 0
            for symbol in productiveSymbol.keys {
                if productiveSymbol[symbol]! { m += 1 }
            }
            
            // finish criteria: productive symbols set is not growing anymore
        } while (n < m)
        
        // production rules result
        //if (n>0) writeln("Grammar contains unproductive production rules!");
        for p in productiveRule.keys {
            if !productiveRule[p]! {
                p.productive = false;
                print("production '\(p)' is a non-productive rule - consider fixing.")
            }
        }
    }


    /// A non-terminal is called reachable or accessible if there exists at least
    /// one sentential form, derivable from the start symbol, in which it occurs.
    /// So a non-terminal A is reachable if S ⇒* αAβ for some α and β.
    /// Traverse grammar foreach nonterminal symbol starting with goal symbol and
    /// for each rule in the grammar of the form A → α with A marked, all non-
    /// terminals in α are marked
    func unreachableNonterminalCheck() {
        // marks reachable grammar nonterminals as true
        var reachableSymbol: [String:Bool] = [:]
        
        // initialize all nonterminals in the grammar to non-reachable
        for symbol in nonterminals { reachableSymbol[symbol] = false }
        
        // start symbol is reachable
        reachableSymbol[S] = true
        
        // loop until set of reachable symbols does not grow anymore
        var n: Int = 0
        var m: Int = 0
        repeat {
            n = m
            for p in productions {
                if reachableSymbol[p.lhs]! {
                    for s in p.rhs {
                        if isNonterminal(symbol: s) {
                            reachableSymbol[s] = true
                        }
                    }
                }
            }
        
            // calculate current cardinality of reachable symbols set
            m = 0
            for symbol in reachableSymbol.keys {
                if reachableSymbol[symbol]! { m += 1 }
            }
         
            // finish criteria: reachable symbols set is not growing anymore
        } while (n < m)
        
        // non reachable symbols result
        //if (n>0) writeln("Grammar contains unreachable nonterminals!");
        for symbol in reachableSymbol.keys {
            if !reachableSymbol[symbol]! {
                print("unreachable nonterminal ' \(symbol)' - consider fixing.")
            }
        }
    }

    /// Check grammar for empty derivations rules
    func emptyDerivationCheck() {
        var visited = Set<String>()

        func checkForEmpty(production p: ProductionRule) {
            if p.derivesEmpty {
                if !symbolDerivesEmpty[p.lhs]! {
                    symbolDerivesEmpty[p.lhs] = true
                    visited.insert(p.lhs)
                }
            }
        }
        
        for nt in nonterminals { symbolDerivesEmpty[nt] = false }
        for p in productions { checkForEmpty(production: p) }
        
        for nt in visited {
            for p in productions {
                if p.containsSymbol(nt).0 {
                    p.epsilon -= 1
                    checkForEmpty(production: p)
                }
            }
        }
    }
    
    /// Check for circular definitions.
    func checkCycles() {
    }
}




extension Grammar {
    
    /// Returns a new unique nonterminal based on the given suggestion.
    private func generateNonterminal(_ suggestion: MetaSymbol) -> String {
        var symbol: String              // prefix of new symbol name
        switch suggestion {
        case .grouping: symbol = "group"
        case .option: symbol = "opt"
        case .repetition: symbol = "rep"
        case .alternation: symbol = "alt"
        }
        symbol += String(counter.increment())
        while isNonterminal(symbol: symbol) { symbol += String(counter.increment()) }
        return symbol
    }
    
    private func outmost(symbols: [String], open: String, close: String) -> ([String],Int,Int)  {
        let stack = Stack<Int>()
        
        for (i,symbol) in symbols.enumerated() {
            if symbol == open {
                stack.push(i)
            }
            else if symbol == close {
                let pos = stack.pop()
                if stack.isEmpty {
                    return (Array(symbols[(pos+1)..<i]), pos, i)
                }
            }
        }
        return ([""],-1,-1);
    }
    
    private func sliceType(p: ProductionRule, low: Int, high: Int) -> Slice {
        if low > 0 && (high+1 < p.symbolCount) { return .middle }
        else if low == 0 && (high+1 < p.symbolCount) { return .low }
        else if low > 0 && (high+1 == p.symbolCount) { return .high }
        else { return .complete }
    }
}


//MARK: Grammar Re-writing

extension Grammar {
    
    // Transforms of extended BNF grammars into standard form.
    // [3] Crafting a compiler
    // 4.3 Transforming Extended Grammars

    /// Rerwite productions that contain grouping constructs of the form
    /// A → α(X1...Xn)β using the following algorithm:
    ///
    /// foreach p ∈ P of the form “A → α(X1...Xn)β” do
    ///     N ← NewNonterminal()
    ///     p ← “ A → α N β ”
    ///     P ← P ∪ { “N → X1...Xn” }
    func rewriteGroupings() {
        var changed = false
        repeat {
            changed = false
            // check for grouping meta characters '(' and ')' in all productions
            for p in productions {
                let match = outmost(symbols: p.rhs,open: reverse[Symbol.lparen]!, close: reverse[Symbol.rparen]!)
                if match.1 != -1 {
                    let low = match.1
                    let high = match.2
                    print("re-writing: \(p) low: \(low) high: \(high)")
                    let N = generateNonterminal(MetaSymbol.grouping)
                    nonterminals.insert(N)
                    let X = match.0
                    
                    // p ← “ A → α N β ” (modify production)
                    switch sliceType(p: p, low: low, high: high) {
                    case .low: p.rhs = [N] + p.rhs[(high+1)...]
                    case .middle: p.rhs = p.rhs[0..<low] + [N] + p.rhs[(high+1)...]
                    case .high: p.rhs = p.rhs[0..<low] + [N]
                    case .complete: p.rhs = [N]
                    }
                    
                    print("modified production 'A → α N β' \(p)")
                    let p1 = createProduction(lhs: N, phrase: X)
                    print("generated production 'N → X1...Xn' \(p1)")
                    changed = true
                }
            }
        } while (changed)
    }
       
    /// Rerwite productions that contain option constructs of the form
    /// A → α[X1...Xn]β using the following algorithm:
    ///
    /// foreach p ∈ P of the form “A → α[X1...Xn]β” do
    ///        N ← NewNonterminal()
    ///        p ← “ A → α N β ”
    ///        P ← P ∪ { “N → X1...Xn” }
    ///        P ← P ∪ { “N → ε” }
    func rewriteOptions() {
        var changed: Bool = false
        repeat {
            changed = false
            // check for option meta characters '[' and ']' in all productions
            for p in productions {
                let match = outmost(symbols: p.rhs,open: reverse[Symbol.lbracket]!, close: reverse[Symbol.rbracket]!)
                if match.1 != -1 {
                    let low = match.1
                    let high = match.2
                    print("re-writing: \(p) low: \(low) high: \(high)")
                    let N = generateNonterminal(MetaSymbol.option)
                    nonterminals.insert(N)
                    let X = match.0
                    print("option construct [X1...Xn] identified: \(X)")
               
                    // p ← “ A → α N β ” (modify production)
                    switch sliceType(p: p, low: low, high: high) {
                    case .low: p.rhs = [N] + p.rhs[(high+1)...]
                    case .middle: p.rhs = p.rhs[..<low] + [N] + p.rhs[(high+1)...]
                    case .high: p.rhs = p.rhs[..<low] + [N]
                    case .complete: p.rhs = [N]
                    }
                    
                    print("modified production 'A → α N β' \(p)")
                    let p1 = createProduction(lhs: N, phrase: X)
                    print("generated production 'N → X1...Xn' \(p1)")
                    let p2 = createProduction(lhs: N, phrase: [Constant.eps])
                    print("generated production 'N → ε' \(p2)")
                    changed = true
                }
            }
        } while (changed)
    }

    /// Rerwite productions that contain repetition constructs of the form
    /// A → γ{X1...Xm}δ using the following algorithm:
    ///
    /// foreach p ∈ P of the form “A → γ{X1...Xm}δ” do
    ///        N ← NewNonterminal()
    ///        p ← “A → γ N δ”
    ///        P ← P ∪ { “N → X1...Xn N” }
    ///        P ← P ∪ { “N → ε” }
    func rewriteRepetitions() {
        var changed = false
        repeat {
            changed = false
            // check for repetition meta characters '{' and '}' in all productions
            for p in productions {
                let match = outmost(symbols: p.rhs, open: reverse[Symbol.lbrace]!, close: reverse[Symbol.rbrace]!)
                if match.1 != -1 {
                    let low = match.1
                    let high = match.2
                    print("re-writing: \(p) low: \(low) high: \(high)")
                    let N = generateNonterminal(MetaSymbol.repetition)
                    nonterminals.insert(N)
                    var X = match.0
                    print("repetition construct {X1...Xn} identified: \(X)")
                    
                    // p ← “A → γ N δ” (modify production)
                    switch sliceType(p: p, low: low, high: high) {
                    case .low: p.rhs = [N] + p.rhs[(high+1)...]
                    case .middle: p.rhs = p.rhs[..<low] + [N] + p.rhs[(high+1)...]
                    case .high: p.rhs = p.rhs[..<low] + [N]
                    case .complete: p.rhs = [N]
                    }
                    
                    print("modified production A → γ N δ: \(p)")
                    X += [N]
                    let p1 = createProduction(lhs: N, phrase: X)
                    print("generated production N → X1...Xn N: \(p1)")
                    let p2 = createProduction(lhs: N, phrase: [Constant.eps])
                    print("generated production N → ε: \(p2)")
                    changed = true
                }
            }
        } while (changed)
    }
       
    /// Rerwite productions that contain repetitions constructs of the form
    /// A ← α | β ··· | ζ by repeating the goal symbol for each alternation
    /// A ← α
    /// A ← β
    ///  ···
    /// A ← ζ
    ///
    /// Note that there may be directly nullable production rules introduced
    /// during rewriting which have to be taken into account.
    func rewriteAlternations() {
        // add all productions into a worklist
        var worklist = [ProductionRule]()
        for p in productions { worklist.append(p) }
        
        // continue while there are items left to process
        while worklist.count > 0 {
            // reduce working list
            let p = worklist.removeFirst()
            let result = p.containsSymbol(reverse[Symbol.or]!)
            if result.0 {
                let prod = createProduction(lhs: p.lhs, phrase: Array(p.rhs[(result.1+1)...]))
                worklist.append(prod)
                
                print("split \(p.lhs) : \(p.rhs[..<result.1])")
                print("split \(p.lhs) : \(prod)")

                // A ← α (modify production, i.e. shorten it)
                p.rhs = Array(p.rhs[..<result.1])
                p.epsilon = p.symbolCount
            }
        }
        
        // adjust epsilon count for directly nullable production rules
        for p in productions {
            if p.containsSymbol(Constant.eps).0 {
                for (_, X) in p.rhs.enumerated() {
                    if X == Constant.eps {
                        p.epsilon = 0
                    }
                }
            }
        }
    }
}




// MARK: First Follow Sets

extension Grammar {

    ///
    private func firstSet() {
        for A in itsProductions.keys {
            firstSets[A] = first(symbol: [A])
        }
    }

    /// Let a ∈ T, A ∈ N,  ωi ∈ ( N ∪ T )
    /// N : set of non-terminal symbols
    /// T : set of terminal symbols
    ///
    /// First(λ) = {λ}
    /// First(a ω) = {a}
    /// If  A -> ω1  | ω2 ......... | ωn
    /// first(A) = first(ω1) ∪ first(ω2) ∪ ... ∪ first(ωn)
    /// Assume ω ≠ λ:
    ///   if λ ∉ first(A), then first(Aω) = first(A)
    ///   if λ ∈ first(A), then first(Aω) = (first(A) - {λ}) ∪ first(ω)
    public func first(symbol: [String]) -> Set<String> {
        var visited = Set<String>()

        func ifirst(_ symbols: [String], set: inout Set<String>) -> Set<String> {
            if symbols.count == 0 { return Set<String>() }
            if symbols[0] == Constant.eps { return Set<String>(arrayLiteral: Constant.eps) }
            if symbols[0] == Constant.eof { return Set<String>(arrayLiteral: Constant.eof) }
            if isTerminal(symbol: symbols[0]) {
                set.insert( symbols[0] )
                return set
            }
            
            // X is a nonterminal.
            if !visited.contains(symbols[0]) {
                visited.insert(symbols[0])
                for p in itsProductions[symbols[0]]! {
                    set.formUnion( ifirst(p.rhs, set: &set) )
                }
            }
            if symbolDerivesEmpty[symbols[0]]! {
                set.formUnion( ifirst(Array(symbols[1...]), set: &set) )
                set.insert( Constant.eps )
            }
            return set
        }
        var set = Set<String>()
        return ifirst(symbol, set: &set)
    }
        
    /// Creates follow set for all nonterminals.
    /// let $ ∈ follow(S)
    /// If A -> α B
    ///    let follow(A) ⊆ follow(B)
    /// If A -> α B β
    ///    λ ∉ first(β), then let first(β) ⊆ follow(B)
    ///    λ ∈ first(β), then let (first (β) - {λ}) ∪ follow(A) ⊆ follow(B)
    public func followSet() {

        func followSetUnion(nonteminal A: String, set: Set<String>) {
            if let i = followSets.index(forKey: A) {
                followSets.values[i].formUnion(set)
            } else {
                followSets[A] = set
            }
        }

        func followSetInsert(nonteminal A: String, element: String) {
            if let i = followSets.index(forKey: A) {
                followSets.values[i].insert(element)
            } else {
                followSets[A] = Set<String>(arrayLiteral: element)
            }
        }

        func followSetCardinality() -> Int {
            var k: Int = 0
            for nt in nonterminals { k += followSets[nt]!.count }
            return k
        }

        func follow(_ nonterminal: String) {
            assert(isNonterminal(symbol: nonterminal))

            for p in productions {
                for (i,B) in p.rhs.enumerated() {
                    if isNonterminal(symbol: B) {
                        let beta = Array( p.rhs[(i+1)...] )
                        if beta.count == 0 {
                            followSetUnion(nonteminal: B, set: followSets[p.lhs]! )
                        } else {
                            if !first(symbol: beta).contains(Constant.eps) {
                                followSetUnion(nonteminal: B, set: first(symbol: beta) )
                            } else {
                                followSetUnion(nonteminal: B, set: followSets[p.lhs]! )
                                var s = first(symbol: beta)
                                s.remove(Constant.eps)
                                followSetUnion(nonteminal: B, set: s )
                            }
                        }
                    }
                }
            }
        }
    
        // initialize dictionary for symbol lookup
        for nt in nonterminals { followSets[nt] = Set<String>() }
        // FOLLOW(S) := { ¶ }, where S is the start symbol
        if S.count > 0 {
            followSetInsert(nonteminal: S, element: Constant.eof)
        }
        
        var n: Int = 0
        var m: Int = 0
        repeat {
            for symbol in nonterminals {
                n = m
                follow(symbol)
                m = followSetCardinality()
            }
        } while (n < m)
    }
}
