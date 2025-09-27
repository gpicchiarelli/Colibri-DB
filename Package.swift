//
//  Package.swift
//  ColibrìDB
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
        .executable(name: "benchmarks-extra", targets: ["benchmarks-extra"]) 
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-testing", exact: "0.10.0")
    ],
    targets: [
        .target(
            name: "CRC32Accelerator",
            publicHeadersPath: "include"
        ),
        .target(
            name: "ColibriCore",
            dependencies: ["CRC32Accelerator"]
        ),
        .executableTarget(
            name: "coldb",
            dependencies: ["ColibriCore"]
        ),
        .executableTarget(
            name: "benchmarks",
            dependencies: ["ColibriCore"]
        ),
        .executableTarget(
            name: "benchmarks-extra",
            dependencies: ["ColibriCore"]
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
