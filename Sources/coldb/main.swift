//
//  main.swift
//  ColibrDB
//
//  Entrypoint for the production `coldb` CLI.
//
import Foundation
import ColibriCLI

do {
    try runColdBCLI(arguments: CommandLine.arguments)
} catch {
    fputs("fatal: \(error)\n", stderr)
    exit(1)
}
