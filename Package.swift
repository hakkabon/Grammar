// swift-tools-version: 5.4
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription

let package = Package(
    name: "Grammar",
    products: [
        .library(name: "Grammar", targets: ["Grammar"])
    ],
    dependencies: [
    ],
    targets: [
        .target(
            name: "Grammar",
            dependencies: []
        ),
        .testTarget(
            name: "GrammarTests",
            dependencies: ["Grammar"]
        ),
    ]
)
