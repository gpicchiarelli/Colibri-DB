//
//  main.swift
//  ColibrDB
//
//  Entrypoint for the production `coldb` CLI.
//
import Foundation
import ColibrìCLI

do {
    try CLIEntryPoint.launch(mode: .production)
} catch {
    fputs("fatal: \(error)\n", stderr)
    exit(1)
}
