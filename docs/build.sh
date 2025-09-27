#!/bin/bash

# ColibrìDB Documentation Build Script

set -e

echo "Building ColibrìDB documentation..."

# Check if Jekyll is installed
if ! command -v jekyll &> /dev/null; then
    echo "Jekyll not found. Installing dependencies..."
    bundle install
fi

# Clean previous build
echo "Cleaning previous build..."
rm -rf _site

# Build documentation
echo "Building documentation..."
bundle exec jekyll build

# Check for broken links
echo "Checking for broken links..."
bundle exec htmlproofer _site --only-4xx --check-html

echo "Documentation built successfully!"
echo "View at: file://$(pwd)/_site/index.html"
