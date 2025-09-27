# ColibrìDB Makefile
# This Makefile provides convenient commands for building, testing, and managing ColibrìDB

.PHONY: help build clean test install uninstall start stop restart status logs dev-setup dev-loop dev-test dev-benchmark dev-telemetry dev-report dev-cleanup

# Default target
help:
	@echo "ColibrìDB Makefile"
	@echo "=================="
	@echo ""
	@echo "Available targets:"
	@echo "  build       Build all targets"
	@echo "  clean       Clean build artifacts"
	@echo "  test        Run all tests"
	@echo "  install     Install ColibrìDB service"
	@echo "  uninstall   Uninstall ColibrìDB service"
	@echo "  start       Start ColibrìDB service"
	@echo "  stop        Stop ColibrìDB service"
	@echo "  restart     Restart ColibrìDB service"
	@echo "  status      Show service status"
	@echo "  logs        Show service logs"
	@echo "  server      Build and run server locally"
	@echo "  test-server Test the HTTP server API"
	@echo ""
	@echo "Development targets:"
	@echo "  dev-setup     Setup development environment"
	@echo "  dev-loop      Run development loop (continuous)"
	@echo "  dev-test      Run comprehensive test suite"
	@echo "  dev-benchmark Run performance benchmarks"
	@echo "  dev-telemetry Collect telemetry data"
	@echo "  dev-report    Generate comprehensive reports"
	@echo "  dev-cleanup   Clean development environment"
	@echo ""
	@echo "  help        Show this help message"
	@echo ""

# Build all targets
build:
	@echo "Building ColibrìDB..."
	swift build --configuration release
	@echo "Build completed successfully"

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	swift package clean
	rm -rf .build
	@echo "Clean completed"

# Run all tests
test:
	@echo "Running tests..."
	swift test
	@echo "Tests completed"

# Install ColibrìDB service
install:
	@echo "Installing ColibrìDB service..."
	sudo ./Scripts/install-service.sh install
	@echo "Installation completed"

# Uninstall ColibrìDB service
uninstall:
	@echo "Uninstalling ColibrìDB service..."
	sudo ./Scripts/install-service.sh uninstall
	@echo "Uninstallation completed"

# Start ColibrìDB service
start:
	@echo "Starting ColibrìDB service..."
	sudo ./Scripts/install-service.sh start
	@echo "Service started"

# Stop ColibrìDB service
stop:
	@echo "Stopping ColibrìDB service..."
	sudo ./Scripts/install-service.sh stop
	@echo "Service stopped"

# Restart ColibrìDB service
restart:
	@echo "Restarting ColibrìDB service..."
	sudo ./Scripts/install-service.sh restart
	@echo "Service restarted"

# Show service status
status:
	@echo "ColibrìDB service status:"
	sudo ./Scripts/install-service.sh status

# Show service logs
logs:
	@echo "ColibrìDB service logs:"
	@echo "======================"
	@echo ""
	@echo "Server log:"
	tail -f /var/log/colibridb/server.log

# Build and run server locally
server: build
	@echo "Starting ColibrìDB server locally..."
	@echo "Server will be available at http://localhost:8080"
	@echo "Press Ctrl+C to stop"
	@echo ""
	.build/release/colibri-server --host localhost --port 8080 --data-dir ./data

# Test the HTTP server API
test-server:
	@echo "Testing ColibrìDB HTTP server API..."
	./Scripts/test-server.sh all

# Test specific endpoint
test-health:
	@echo "Testing health endpoint..."
	./Scripts/test-server.sh health

# Test database operations
test-database:
	@echo "Testing database operations..."
	./Scripts/test-server.sh database

# Test table operations
test-table:
	@echo "Testing table operations..."
	./Scripts/test-server.sh table

# Test query operations
test-query:
	@echo "Testing query operations..."
	./Scripts/test-server.sh query

# Test transaction operations
test-transaction:
	@echo "Testing transaction operations..."
	./Scripts/test-server.sh transaction

# Test index operations
test-index:
	@echo "Testing index operations..."
	./Scripts/test-server.sh index

# Test monitoring operations
test-monitoring:
	@echo "Testing monitoring operations..."
	./Scripts/test-server.sh monitoring

# Test testing operations
test-testing:
	@echo "Testing testing operations..."
	./Scripts/test-server.sh testing

# Test performance operations
test-performance:
	@echo "Testing performance operations..."
	./Scripts/test-server.sh performance

# Run load test
test-load:
	@echo "Running load test..."
	./Scripts/test-server.sh load

# Build and run development tools
dev: build
	@echo "Starting ColibrìDB development tools..."
	.build/release/coldb-dev

# Build and run CLI
cli: build
	@echo "Starting ColibrìDB CLI..."
	.build/release/coldb

# Create release package
release: clean build
	@echo "Creating release package..."
	mkdir -p release
	cp .build/release/colibri-server release/
	cp .build/release/coldb-dev release/
	cp .build/release/coldb release/
	cp -r Scripts release/
	cp -r Resources release/
	cp -r Examples release/
	cp -r docs release/
	cp README.md release/
	cp LICENSE release/
	cp Package.swift release/
	tar -czf colibridb-$(shell date +%Y%m%d).tar.gz -C release .
	@echo "Release package created: colibridb-$(shell date +%Y%m%d).tar.gz"

# Install dependencies
deps:
	@echo "Installing dependencies..."
	brew install jq
	@echo "Dependencies installed"

# Setup development environment
setup: deps
	@echo "Setting up development environment..."
	mkdir -p data
	mkdir -p logs
	@echo "Development environment ready"

# Full installation and test
install-test: install start
	@echo "Waiting for service to start..."
	sleep 5
	@echo "Running tests..."
	./Scripts/test-server.sh all
	@echo "Installation and testing completed"

# Quick start (build, run locally, test)
quick: build server-test
	@echo "Quick start completed"

# Server test (assumes server is running)
server-test:
	@echo "Testing server..."
	./Scripts/test-server.sh all

# Development environment setup
dev-setup:
	@echo "Setting up ColibrìDB development environment..."
	@chmod +x Scripts/dev-environment.sh
	@./Scripts/dev-environment.sh
	@echo "Development environment setup complete"

# Development loop (continuous)
dev-loop:
	@echo "Starting ColibrìDB development loop..."
	@chmod +x Scripts/development-loop.sh
	@./Scripts/development-loop.sh --continuous --verbose

# Development loop (single iteration)
dev-loop-single:
	@echo "Running single development iteration..."
	@chmod +x Scripts/development-loop.sh
	@./Scripts/development-loop.sh --iterations 1 --verbose

# Comprehensive test suite
dev-test:
	@echo "Running comprehensive test suite..."
	@chmod +x Scripts/run-tests-simple.sh
	@./Scripts/run-tests-simple.sh --verbose --coverage --parallel

# Performance benchmarks
dev-benchmark:
	@echo "Running performance benchmarks..."
	@chmod +x Scripts/run-benchmarks-simple.sh
	@./Scripts/run-benchmarks-simple.sh --verbose --format json

# Telemetry collection
dev-telemetry:
	@echo "Collecting telemetry data..."
	@chmod +x Scripts/collect-telemetry-simple.sh
	@./Scripts/collect-telemetry-simple.sh --verbose --duration 300

# Generate reports
dev-report:
	@echo "Generating comprehensive reports..."
	@chmod +x Scripts/generate-report-simple.sh
	@./Scripts/generate-report-simple.sh --verbose --format html

# Cleanup development environment
dev-cleanup:
	@echo "Cleaning development environment..."
	@chmod +x Scripts/cleanup.sh
	@./Scripts/cleanup.sh --all --verbose

# Full development cycle
dev-cycle: dev-setup dev-test dev-benchmark dev-telemetry dev-report
	@echo "Full development cycle completed"

# Quick development test
dev-quick: build dev-test
	@echo "Quick development test completed"

# Show all available commands
commands:
	@echo "Available commands:"
	@echo "==================="
	@echo ""
	@echo "Build commands:"
	@echo "  make build          - Build all targets"
	@echo "  make clean          - Clean build artifacts"
	@echo "  make release        - Create release package"
	@echo ""
	@echo "Service commands:"
	@echo "  make install        - Install as system service"
	@echo "  make uninstall      - Uninstall system service"
	@echo "  make start          - Start service"
	@echo "  make stop           - Stop service"
	@echo "  make restart        - Restart service"
	@echo "  make status         - Show service status"
	@echo "  make logs           - Show service logs"
	@echo ""
	@echo "Development commands:"
	@echo "  make server         - Run server locally"
	@echo "  make dev            - Run development tools"
	@echo "  make cli            - Run CLI"
	@echo ""
	@echo "Development Environment:"
	@echo "  make dev-setup      - Setup development environment"
	@echo "  make dev-loop       - Run continuous development loop"
	@echo "  make dev-loop-single - Run single development iteration"
	@echo "  make dev-test       - Run comprehensive test suite"
	@echo "  make dev-benchmark  - Run performance benchmarks"
	@echo "  make dev-telemetry  - Collect telemetry data"
	@echo "  make dev-report     - Generate comprehensive reports"
	@echo "  make dev-cleanup    - Clean development environment"
	@echo "  make dev-cycle      - Run full development cycle"
	@echo "  make dev-quick      - Quick development test"
	@echo ""
	@echo "Testing commands:"
	@echo "  make test           - Run unit tests"
	@echo "  make test-server    - Test HTTP API"
	@echo "  make test-health    - Test health endpoint"
	@echo "  make test-database  - Test database operations"
	@echo "  make test-table     - Test table operations"
	@echo "  make test-query     - Test query operations"
	@echo "  make test-transaction - Test transaction operations"
	@echo "  make test-index     - Test index operations"
	@echo "  make test-monitoring - Test monitoring operations"
	@echo "  make test-testing   - Test testing operations"
	@echo "  make test-performance - Test performance operations"
	@echo "  make test-load      - Run load test"
	@echo ""
	@echo "Setup commands:"
	@echo "  make setup          - Setup development environment"
	@echo "  make deps           - Install dependencies"
	@echo "  make install-test   - Install service and run tests"
	@echo "  make quick          - Quick start (build, run, test)"
	@echo ""
	@echo "Smart testing commands:"
	@echo "  make smart-test     - Run smart continuous testing with error correction"
	@echo "  make smart-test-iterations ITERATIONS=N - Run with N iterations"
	@echo "  make smart-test-interval INTERVAL=N - Run with N second interval"
	@echo "  make smart-test-custom ITERATIONS=N INTERVAL=M - Run with custom parameters"

# Smart testing targets
smart-test: ## Run smart continuous testing with error correction
	@echo "Starting smart continuous testing..."
	@chmod +x Scripts/smart-continuous-testing.sh
	@./Scripts/smart-continuous-testing.sh
	@echo "Smart testing complete"

smart-test-iterations: ## Run smart testing with custom iterations (usage: make smart-test-iterations ITERATIONS=5)
	@echo "Starting smart continuous testing with $(ITERATIONS) iterations..."
	@chmod +x Scripts/smart-continuous-testing.sh
	@./Scripts/smart-continuous-testing.sh -i $(ITERATIONS)
	@echo "Smart testing complete"

smart-test-interval: ## Run smart testing with custom interval (usage: make smart-test-interval INTERVAL=60)
	@echo "Starting smart continuous testing with $(INTERVAL)s interval..."
	@chmod +x Scripts/smart-continuous-testing.sh
	@./Scripts/smart-continuous-testing.sh -t $(INTERVAL)
	@echo "Smart testing complete"

smart-test-custom: ## Run smart testing with custom parameters (usage: make smart-test-custom ITERATIONS=3 INTERVAL=45)
	@echo "Starting smart continuous testing with $(ITERATIONS) iterations and $(INTERVAL)s interval..."
	@chmod +x Scripts/smart-continuous-testing.sh
	@./Scripts/smart-continuous-testing.sh -i $(ITERATIONS) -t $(INTERVAL)
	@echo "Smart testing complete"
