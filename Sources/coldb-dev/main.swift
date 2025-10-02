//
//  main.swift
//  coldb-dev
//
//  Thin executable wrapper around the ColibriDevTools module.
//
import Foundation
import ColibrìCLI

do {
    let configPath = CommandLine.arguments.count > 1 ? CommandLine.arguments[1] : nil
    try CLIEntryPoint.launch(mode: .development, configPath: configPath)
} catch {
    fputs("fatal: \(error)\n", stderr)
    exit(1)
}
