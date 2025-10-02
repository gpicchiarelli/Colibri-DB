import XCTest
import Darwin
@testable import ColibriDevTools
import ColibriCore

final class DevCLITests: XCTestCase {
    private var database: Database!
    private var cli: DevCLI!
    private var tempDirectory: URL!

    override func setUpWithError() throws {
        tempDirectory = FileManager.default.temporaryDirectory.appendingPathComponent("colibridb-devtools-tests-\(UUID().uuidString)")
        try FileManager.default.createDirectory(at: tempDirectory, withIntermediateDirectories: true)

        var config = DBConfig(dataDir: tempDirectory.path)
        config.maxConnectionsLogical = 16
        config.maxConnectionsPhysical = 4
        database = Database(config: config)
        try database.ensureDataDir()
        cli = DevCLI(db: database, cfgPath: tempDirectory.path)
    }

    override func tearDownWithError() throws {
        if let dir = tempDirectory {
            try? FileManager.default.removeItem(at: dir)
        }
        database = nil
        cli = nil
        tempDirectory = nil
    }

    func testBannerDisplaysTitle() {
        let output = captureOutput {
            cli.printBanner()
        }
        XCTAssertTrue(output.contains("ColibrDB Dev CLI"))
        XCTAssertTrue(output.contains("Development Version"))
    }

    func testHelpListsPrimarySections() {
        let output = captureOutput {
            cli.help()
        }
        XCTAssertTrue(output.contains("Commands:"))
        XCTAssertTrue(output.contains("\\help"))
        XCTAssertTrue(output.contains("\\insert"))
        XCTAssertTrue(output.contains("\\benchmark"))
    }

    func testConfigMentionsDataDirectory() {
        let output = captureOutput {
            cli.showConfig()
        }
        XCTAssertTrue(output.contains(tempDirectory.path))
    }

    @MainActor func testParseAndRunHandlesKnownCommand() {
        var mutableCLI = cli!
        let output = captureOutput {
            mutableCLI.parseAndRun("\\help")
        }
        XCTAssertTrue(output.contains("Commands:"))
    }

    @MainActor func testParseAndRunRejectsUnknownCommand() {
        var mutableCLI = cli!
        let output = captureOutput {
            mutableCLI.parseAndRun("\\totally_unknown")
        }
        XCTAssertTrue(output.contains("Unrecognized command"))
    }

    func testTestRunnerProducesResults() {
        let runner = TestRunner(database: database)
        let unitResults = runner.runUnitTests()
        XCTAssertFalse(unitResults.isEmpty)
        let all = runner.runAllTests()
        XCTAssertEqual(all.totalTests, all.passedTests + all.failedTests)
    }

    // MARK: - Helpers

    private func captureOutput(_ block: () -> Void) -> String {
        let pipe = Pipe()
        let originalStdout = dup(fileno(stdout))
        fflush(stdout)
        dup2(pipe.fileHandleForWriting.fileDescriptor, fileno(stdout))

        block()

        fflush(stdout)
        dup2(originalStdout, fileno(stdout))
        close(originalStdout)

        let data = pipe.fileHandleForReading.readDataToEndOfFile()
        pipe.fileHandleForWriting.closeFile()
        return String(data: data, encoding: .utf8) ?? ""
    }
}
