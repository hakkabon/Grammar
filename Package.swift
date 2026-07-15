// swift-tools-version:5.9
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription

let package = Package(
    name: "Grammar",
    platforms: [.macOS(.v11), .iOS(.v14)],
    products: [
        .library(name: "Grammar", targets: ["Grammar"])
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-argument-parser.git", from: "1.6.2"),
        .package(url: "https://github.com/apple/swift-algorithms", from: "1.2.1"),
        .package(url: "https://github.com/hakkabon/GrammarTokenizer.git", branch: "main"),
        .package(url: "https://github.com/hakkabon/GrammarDiagram.git", branch: "main"),
        .package(url: "https://github.com/hakkabon/TerminalColors.git", branch: "main"),
    ],
    targets: [
        .target(name: "Grammar", dependencies: [
            .product(name: "Algorithms", package: "swift-algorithms"),
            .product(name: "Tokenizer", package: "GrammarTokenizer"),
            .product(name: "GrammarDiagram", package: "GrammarDiagram"),
            .product(name: "TerminalColors", package: "TerminalColors"),
        ]),
        .testTarget(name: "GrammarTests", dependencies: [
            "Grammar",
            .product(name: "Algorithms", package: "swift-algorithms"),
        ]),
        // Move executable target to its destination (grammar toolbox) when library confirmed working.
        .executableTarget(
            name: "gtool", dependencies: [
                "Grammar",
                .product(name: "Tokenizer", package: "GrammarTokenizer"),
                .product(name: "GrammarDiagram", package: "GrammarDiagram"),
                .product(name: "TerminalColors", package: "TerminalColors"),
                .product(name: "ArgumentParser", package: "swift-argument-parser")
        ]),
    ]
)
