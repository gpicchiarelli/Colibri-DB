#!/bin/bash

# Install dependencies for GitHub Actions workflows
# This script handles both macOS and Linux platforms

set -e

echo "🔧 Installing dependencies for ${{ runner.os }}..."

# Install jq (required for JSON processing)
if [[ "${{ runner.os }}" == "macOS" ]]; then
    echo "Installing jq via Homebrew..."
    brew install jq
else
    echo "Installing jq via apt..."
    sudo apt-get update
    sudo apt-get install -y jq
fi

# Install SwiftLint
if [[ "${{ runner.os }}" == "macOS" ]]; then
    echo "Installing SwiftLint via Homebrew..."
    brew install swiftlint
else
    echo "Installing SwiftLint via direct download..."
    curl -sL https://github.com/realm/SwiftLint/releases/latest/download/portable_swiftlint.zip | bsdtar -xzf - -C /usr/local/bin
    chmod +x /usr/local/bin/swiftlint
fi

# Install SwiftFormat
if [[ "${{ runner.os }}" == "macOS" ]]; then
    echo "Installing SwiftFormat via Homebrew..."
    brew install swiftformat
else
    echo "Installing SwiftFormat via direct download..."
    curl -sL https://github.com/nicklockwood/SwiftFormat/releases/latest/download/swiftformat_linux.zip | bsdtar -xzf - -C /usr/local/bin
    chmod +x /usr/local/bin/swiftformat
fi

echo "✅ All dependencies installed successfully"