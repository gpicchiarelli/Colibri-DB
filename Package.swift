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
        .executable(name: "coldb", targets: ["coldb"]),
        .executable(name: "coldb-server", targets: ["coldb-server"]),
        .executable(name: "benchmarks", targets: ["benchmarks"]) 
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-testing", exact: "0.10.0"),
        .package(url: "https://github.com/apple/swift-nio.git", from: "2.65.0"),
        .package(url: "https://github.com/apple/swift-nio-ssl.git", from: "2.25.0"),
        .package(url: "https://github.com/apple/swift-atomics.git", from: "1.0.3")
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
        .executableTarget(
            name: "coldb",
            dependencies: ["ColibriCore"],
            exclude: ["README.md"]
        ),
        .executableTarget(
            name: "coldb-server",
            dependencies: [
                "ColibriCore",
                .product(name: "NIO", package: "swift-nio"),
                .product(name: "NIOHTTP1", package: "swift-nio"),
                .product(name: "NIOSSL", package: "swift-nio-ssl")
            ],
            exclude: ["README.md"]
        ),
        .executableTarget(
            name: "benchmarks",
            dependencies: [
                "ColibriCore",
                .product(name: "Atomics", package: "swift-atomics")
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
