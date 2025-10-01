//
//  main.swift
//  coldb-dev
//
//  Thin executable wrapper around the ColibriDevTools module.
//
import Foundation
import ColibriDevTools

do {
    try runColdBDevCLI(arguments: CommandLine.arguments)
} catch {
    fputs("fatal: \(error)\n", stderr)
    exit(1)
}
