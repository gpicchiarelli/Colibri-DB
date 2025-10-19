//
//  Package.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// swift-tools-version: 6.0

// Theme: Manifest conductor orchestrating modules and dependencies.

import PackageDescription

let package = Package(
    name: "ColibriDB",
    platforms: [
        .macOS(.v13)
    ],
    products: [
        .library(name: "ColibriCore", targets: ["ColibriCore"]),
        .library(name: "ColibriCLI", targets: ["ColibriCLI"]),
        .library(name: "ColibriServer", targets: ["ColibriServer"]),
        .executable(name: "coldb", targets: ["coldb"]),
        .executable(name: "coldb-server", targets: ["coldb-server"]),
        .executable(name: "coldb-dev", targets: ["coldb-dev"]),
        .executable(name: "benchmarks", targets: ["benchmarks"]),
        .executable(name: "test-gc", targets: ["test-gc"])
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-testing", exact: "0.10.0"),
        .package(url: "https://github.com/apple/swift-nio.git", from: "2.65.0"),
        .package(url: "https://github.com/apple/swift-nio-ssl.git", from: "2.25.0"),
        .package(url: "https://github.com/apple/swift-atomics.git", from: "1.3.0")
    ],
    targets: [
        .target(
            name: "CRC32Accelerator",
            publicHeadersPath: "include"
        ),
        .target(
            name: "ColibriCore",
            dependencies: ["CRC32Accelerator"],
            exclude: ["README.md"]
        ),
        .target(
            name: "ColibriCLI",
            dependencies: ["ColibriCore"]
        ),
        .target(
            name: "ColibriServer",
            dependencies: [
                "ColibriCore",
                .product(name: "NIO", package: "swift-nio"),
                .product(name: "NIOHTTP1", package: "swift-nio"),
                .product(name: "NIOSSL", package: "swift-nio-ssl")
            ],
            exclude: ["README.md"]
        ),
        .executableTarget(
            name: "coldb",
            dependencies: ["ColibriCLI"]
        ),
        .executableTarget(
            name: "coldb-server",
            dependencies: ["ColibriServer"]
        ),
        .executableTarget(
            name: "coldb-dev",
            dependencies: ["ColibriCLI"]
        ),
        .executableTarget(
            name: "benchmarks",
            dependencies: [
                "ColibriCore",
                .product(name: "Atomics", package: "swift-atomics")
            ]
        ),
        .executableTarget(
            name: "test-gc",
            dependencies: [
                "ColibriCore"
            ]
        ),
        .testTarget(
            name: "ColibriCoreTests",
            dependencies: [
                "ColibriCore",
                .product(name: "Testing", package: "swift-testing")
            ]
        )
    ]
)
