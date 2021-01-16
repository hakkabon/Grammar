import ArgumentParser
import Files
import Grammar
import BNF
    
struct GrammarTool: ParsableCommand {

    @Argument(help: "Grammar file name")
    var grammar: String
    
    @Flag(name: [.short, .long], help: "Trace execution")
    var trace: Bool = false
    
    @Flag(name: [.short, .long], help: "grammar diagnostics")
    var diagnostics: Bool = false

    mutating func run() throws {
        do {
            let gr = try Grammar(grammar: File(path: grammar))
            if diagnostics {
                gr.printGrammar(detail: .full)
            }
        } catch (let error) {
            print("\(error.localizedDescription)")
        }
    }
}

GrammarTool.main()
