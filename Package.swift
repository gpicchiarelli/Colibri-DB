//
//  Package.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
//  A high-performance relational database management system written in Swift 6.0
//  with formal verification using TLA+ specifications.
//
// swift-tools-version: 6.2

import PackageDescription

let package = Package(
    name: "ColibriDB",
    platforms: [
        .macOS(.v13)
    ],
    products: [
        .library(name: "ColibriCore", targets: ["ColibriCore"]),
        .library(name: "ColibriServer", targets: ["ColibriServer"]),
        .executable(name: "coldb", targets: ["coldb"]),
        .executable(name: "coldb-server", targets: ["coldb-server"]),
        .executable(name: "benchmarks", targets: ["benchmarks"])
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-log.git", from: "1.6.0"),
        .package(url: "https://github.com/apple/swift-nio.git", from: "2.65.0"),
        .package(url: "https://github.com/apple/swift-crypto.git", from: "4.0.0")
    ],
    targets: [
        .target(
            name: "CRC32Accelerator",
            publicHeadersPath: "include"
        ),
        .target(
            name: "ColibriCore",
            dependencies: [
                .product(name: "Logging", package: "swift-log"),
                .product(name: "Crypto", package: "swift-crypto"),
                "CRC32Accelerator"
            ]
        ),
        .target(
            name: "ColibriServer",
            dependencies: [
                "ColibriCore",
                .product(name: "NIO", package: "swift-nio"),
                .product(name: "NIOHTTP1", package: "swift-nio")
            ]
        ),
        .executableTarget(
            name: "coldb",
            dependencies: ["ColibriCore"]
        ),
        .executableTarget(
            name: "coldb-server",
            dependencies: ["ColibriServer"]
        ),
        .executableTarget(
            name: "benchmarks",
            dependencies: ["ColibriCore"]
        ),
        .testTarget(
            name: "ColibriCoreTests",
            dependencies: ["ColibriCore"]
        )
    ]
)
