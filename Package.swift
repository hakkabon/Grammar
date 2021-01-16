// swift-tools-version:5.3
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription

let package = Package(
    name: "Grammar",
    products: [
        .library(name: "Grammar", targets: ["Grammar"])
    ],
    dependencies: [
        .package(name: "Files", url: "https://github.com/johnsundell/files.git", from: "2.2.1"),
        .package(url: "https://github.com/apple/swift-argument-parser", from: "0.3.0"),
        .package(name: "BNF", url: "https://github.com/hakkabon/BNF-Parser", from: "1.0.0"),
    ],
    targets: [
        .target(name: "Grammar", dependencies: ["BNF", "Files"]),
        .target(name: "grm", dependencies: ["Grammar", "Files",
                .product(name: "ArgumentParser", package: "swift-argument-parser")]),
        .testTarget(name: "GrammarTests", dependencies: ["Grammar"]),
    ]
)
