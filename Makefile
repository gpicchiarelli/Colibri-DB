.PHONY: build test clean help format lint benchmark install uninstall

# Default target
all: build

# Build the project
build:
	@echo "🔨 Building ColibrìDB..."
	swift build

# Run tests
test:
	@echo "🧪 Running tests..."
	swift test

# Run benchmarks
benchmark:
	@echo "📊 Running benchmarks..."
	swift run benchmarks

# Format code
format:
	@echo "🎨 Formatting code..."
	swiftformat .

# Lint code
lint:
	@echo "🔍 Linting code..."
	swiftlint

# Clean build artifacts
clean:
	@echo "🧹 Cleaning build artifacts..."
	swift package clean

# Install CLI tools
install: build
	@echo "📦 Installing ColibrìDB CLI..."
	cp .build/debug/coldb /usr/local/bin/
	cp .build/debug/coldb-server /usr/local/bin/
	cp .build/debug/coldb-dev /usr/local/bin/

# Uninstall CLI tools
uninstall:
	@echo "🗑️ Uninstalling ColibrìDB CLI..."
	rm -f /usr/local/bin/coldb
	rm -f /usr/local/bin/coldb-server
	rm -f /usr/local/bin/coldb-dev

# Quality check (format + lint + test)
quality: format lint test
	@echo "✅ Quality check completed"

# Show help
help:
	@echo "🐦 ColibrìDB Makefile"
	@echo ""
	@echo "Available targets:"
	@echo "  build      - Build the project"
	@echo "  test       - Run tests"
	@echo "  benchmark  - Run benchmarks"
	@echo "  format     - Format code with SwiftFormat"
	@echo "  lint       - Lint code with SwiftLint"
	@echo "  clean      - Clean build artifacts"
	@echo "  install    - Install CLI tools to /usr/local/bin"
	@echo "  uninstall  - Remove CLI tools from /usr/local/bin"
	@echo "  quality    - Run format, lint, and test"
	@echo "  help       - Show this help message"
	@echo ""
	@echo "Examples:"
	@echo "  make quality    # Run all quality checks"
	@echo "  make install    # Build and install CLI tools"

