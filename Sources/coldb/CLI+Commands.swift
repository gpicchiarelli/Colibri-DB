//
//  CLI+Commands.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: CLI command implementations organized by functionality.

import Foundation
import ColibriCore

// MARK: - Basic Commands
extension CLI {
    /// Lists every CLI command along with a short description.
    func help() {
        print("Commands:")
        print("  \\help                              Show this help")
        print("  \\conf                              Show active configuration")
        print("  \\dt                                List tables")
        print("  \\create table <name>               Create table (heap)")
        print("  \\begin                            Begin transaction")
        print("  \\commit [tid]                     Commit (current or given tid)")
        print("  \\rollback [tid]                   Rollback (current or given tid)")
        print("  \\insert <table> col=val,...        Insert a row")
        print("  \\delete <table> col=val[,col2=val2] Delete rows by equality (uses indexes)")
        print("  \\scan <table>                      Scan and print rows")
        print("  \\create index <name> ON <table>(<col>) USING <Hash|ART|BTree>")
        print("  \\indexes <table>                   List indexes on table")
        print("  \\index search <table> <index> <value>")
        print("  \\index range <table> <index> <lo> <hi>")
        print("  \\index validate <table> <index>")
        print("  \\index rebuild <table> <index>")
        print("  \\index validate-deep <table> <index>")
        print("  \\index rebuild-bulk <table> <index>")
        print("  \\index dump-header <table> <index> [pageId]")
        print("  \\index dump-leaves <table> <index> [count]")
        print("  \\index compact <table> <index>     Compact persistent index file")
        print("  \\flush all                         Flush all buffers")
        print("  \\flush table <table>               Flush table buffers")
        print("  \\flush index <table> <index>       Flush index buffers")
        print("  \\bp                                 Buffer pool stats (tables + indexes)")
        print("  \\stats                              Aggregate metrics (buffers, vacuum)")
        print("  \\table compact <table> [pageId]     Compact heap page(s)")
        print("  \\vacuum start [sec] [pages]        Start periodic vacuum")
        print("  \\vacuum stop                       Stop periodic vacuum")
        print("  \\vacuum stats                      Show vacuum stats")
        print("  \\checkpoint                        Checkpoint DB (truncate WAL)")
        print("  \\policy add time-window <table> [BY col1,col2] WINDOW hh:mm-hh:mm")
        print("  \\policy add load-threshold <table> THRESHOLD qps=100,cpu=20%")
        print("  \\policy add fragmentation <table> THRESHOLD 30%")
        print("  \\policy list                        List policies")
        print("  \\policy remove <uuid>               Remove policy by id")
        print("  \\optimize simulate <table> [BY col1,col2]")
        print("  \\import <file.csv> INTO <table>     Import CSV (header row, simple CSV)")
        print("  \\export <table> TO <file.csv>       Export table to CSV")
        print("  \\stats prometheus                   Print Prometheus metrics")
        print("  \\exit                              Quit")
    }

    /// Prints the active configuration values and source file.
    func showConfig() {
        let cfg = db.config
        print("Configuration: dataDir=\(cfg.dataDir) logical=\(cfg.maxConnectionsLogical) physical=\(cfg.maxConnectionsPhysical) page=\(cfg.pageSizeBytes) index=\(cfg.indexImplementation) wal=\(cfg.walEnabled) checksum=\(cfg.checksumEnabled)")
        if let path = cfgPath { print("Loaded from: \(path)") }
    }

    /// Outputs all registered tables in the catalog.
    func listTables() {
        let ts = db.listTables()
        if ts.isEmpty { print("(no tables)") } else { ts.forEach { print($0) } }
    }
}
