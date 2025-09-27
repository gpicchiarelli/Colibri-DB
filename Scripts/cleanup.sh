#!/bin/bash

# ColibrìDB Cleanup Script
# Comprehensive cleanup and reset system

set -e

# Configuration
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEV_DIR="$PROJECT_ROOT/dev-environment"
DATA_DIR="$DEV_DIR/data"
LOGS_DIR="$DEV_DIR/logs"
REPORTS_DIR="$DEV_DIR/reports"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Cleanup options
CLEAN_DATA=false
CLEAN_LOGS=false
CLEAN_REPORTS=false
CLEAN_BUILD=false
CLEAN_ALL=false
FORCE=false
VERBOSE=false

# Functions
log() {
    echo -e "${BLUE}[$(date +'%Y-%m-%d %H:%M:%S')]${NC} $1"
}

success() {
    echo -e "${GREEN}[$(date +'%Y-%m-%d %H:%M:%S')] ✓${NC} $1"
}

warning() {
    echo -e "${YELLOW}[$(date +'%Y-%m-%d %H:%M:%S')] ⚠${NC} $1"
}

error() {
    echo -e "${RED}[$(date +'%Y-%m-%d %H:%M:%S')] ✗${NC} $1"
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --data)
            CLEAN_DATA=true
            shift
            ;;
        --logs)
            CLEAN_LOGS=true
            shift
            ;;
        --reports)
            CLEAN_REPORTS=true
            shift
            ;;
        --build)
            CLEAN_BUILD=true
            shift
            ;;
        --all)
            CLEAN_ALL=true
            shift
            ;;
        --force)
            FORCE=true
            shift
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        --help)
            echo "Usage: $0 [options]"
            echo "Options:"
            echo "  --data      Clean data directories"
            echo "  --logs      Clean log files"
            echo "  --reports   Clean report files"
            echo "  --build     Clean build artifacts"
            echo "  --all       Clean everything"
            echo "  --force     Force cleanup without confirmation"
            echo "  --verbose   Verbose output"
            echo "  --help      Show this help"
            exit 0
            ;;
        *)
            error "Unknown option: $1"
            exit 1
            ;;
    esac
done

# If no specific options, clean all
if [ "$CLEAN_DATA" = false ] && [ "$CLEAN_LOGS" = false ] && [ "$CLEAN_REPORTS" = false ] && [ "$CLEAN_BUILD" = false ] && [ "$CLEAN_ALL" = false ]; then
    CLEAN_ALL=true
fi

# Function to confirm cleanup
confirm_cleanup() {
    if [ "$FORCE" = true ]; then
        return 0
    fi
    
    local message="$1"
    echo -e "${YELLOW}Are you sure you want to $message? (y/N)${NC}"
    read -r response
    case $response in
        [yY][eE][sS]|[yY])
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

# Function to clean data directories
clean_data() {
    log "Cleaning data directories..."
    
    if [ -d "$DATA_DIR" ]; then
        if confirm_cleanup "remove all data files"; then
            rm -rf "$DATA_DIR"/*
            success "Data directories cleaned"
        else
            warning "Data cleanup cancelled"
        fi
    else
        warning "Data directory not found: $DATA_DIR"
    fi
}

# Function to clean log files
clean_logs() {
    log "Cleaning log files..."
    
    if [ -d "$LOGS_DIR" ]; then
        if confirm_cleanup "remove all log files"; then
            find "$LOGS_DIR" -type f -name "*.log" -delete
            find "$LOGS_DIR" -type f -name "*.out" -delete
            find "$LOGS_DIR" -type f -name "*.err" -delete
            success "Log files cleaned"
        else
            warning "Log cleanup cancelled"
        fi
    else
        warning "Log directory not found: $LOGS_DIR"
    fi
}

# Function to clean report files
clean_reports() {
    log "Cleaning report files..."
    
    if [ -d "$REPORTS_DIR" ]; then
        if confirm_cleanup "remove all report files"; then
            rm -rf "$REPORTS_DIR"/*
            success "Report files cleaned"
        else
            warning "Report cleanup cancelled"
        fi
    else
        warning "Report directory not found: $REPORTS_DIR"
    fi
}

# Function to clean build artifacts
clean_build() {
    log "Cleaning build artifacts..."
    
    if confirm_cleanup "remove all build artifacts"; then
        # Clean Swift build artifacts
        if [ -d "$PROJECT_ROOT/.build" ]; then
            rm -rf "$PROJECT_ROOT/.build"
            success "Swift build artifacts cleaned"
        fi
        
        # Clean Xcode build artifacts
        if [ -d "$PROJECT_ROOT/build" ]; then
            rm -rf "$PROJECT_ROOT/build"
            success "Xcode build artifacts cleaned"
        fi
        
        # Clean derived data
        if [ -d "$PROJECT_ROOT/DerivedData" ]; then
            rm -rf "$PROJECT_ROOT/DerivedData"
            success "Derived data cleaned"
        fi
        
        # Clean temporary files
        find "$PROJECT_ROOT" -name "*.tmp" -delete
        find "$PROJECT_ROOT" -name "*.temp" -delete
        find "$PROJECT_ROOT" -name ".DS_Store" -delete
        
        success "Build artifacts cleaned"
    else
        warning "Build cleanup cancelled"
    fi
}

# Function to clean everything
clean_all() {
    log "Cleaning everything..."
    
    if confirm_cleanup "remove all development environment data"; then
        # Stop any running processes
        log "Stopping running processes..."
        pkill -f "colibri-server" 2>/dev/null || true
        pkill -f "coldb" 2>/dev/null || true
        pkill -f "coldb-dev" 2>/dev/null || true
        
        # Clean all directories
        clean_data
        clean_logs
        clean_reports
        clean_build
        
        # Clean development environment
        if [ -d "$DEV_DIR" ]; then
            rm -rf "$DEV_DIR"
            success "Development environment cleaned"
        fi
        
        success "Complete cleanup finished"
    else
        warning "Complete cleanup cancelled"
    fi
}

# Function to show cleanup summary
show_summary() {
    log "Cleanup Summary:"
    
    if [ "$CLEAN_DATA" = true ] || [ "$CLEAN_ALL" = true ]; then
        echo "  ✓ Data directories"
    fi
    
    if [ "$CLEAN_LOGS" = true ] || [ "$CLEAN_ALL" = true ]; then
        echo "  ✓ Log files"
    fi
    
    if [ "$CLEAN_REPORTS" = true ] || [ "$CLEAN_ALL" = true ]; then
        echo "  ✓ Report files"
    fi
    
    if [ "$CLEAN_BUILD" = true ] || [ "$CLEAN_ALL" = true ]; then
        echo "  ✓ Build artifacts"
    fi
}

# Function to show disk usage
show_disk_usage() {
    log "Disk usage before cleanup:"
    
    if [ -d "$DEV_DIR" ]; then
        du -sh "$DEV_DIR" 2>/dev/null || echo "  Unable to calculate disk usage"
    fi
    
    if [ -d "$PROJECT_ROOT/.build" ]; then
        du -sh "$PROJECT_ROOT/.build" 2>/dev/null || echo "  Unable to calculate build size"
    fi
}

# Function to show disk usage after cleanup
show_disk_usage_after() {
    log "Disk usage after cleanup:"
    
    if [ -d "$DEV_DIR" ]; then
        du -sh "$DEV_DIR" 2>/dev/null || echo "  Development directory not found"
    fi
    
    if [ -d "$PROJECT_ROOT/.build" ]; then
        du -sh "$PROJECT_ROOT/.build" 2>/dev/null || echo "  Build directory not found"
    fi
}

# Main cleanup execution
main() {
    log "Starting ColibrìDB cleanup..."
    log "Project root: $PROJECT_ROOT"
    log "Development directory: $DEV_DIR"
    
    # Show current disk usage
    show_disk_usage
    
    # Show what will be cleaned
    show_summary
    
    # Execute cleanup based on options
    if [ "$CLEAN_ALL" = true ]; then
        clean_all
    else
        if [ "$CLEAN_DATA" = true ]; then
            clean_data
        fi
        
        if [ "$CLEAN_LOGS" = true ]; then
            clean_logs
        fi
        
        if [ "$CLEAN_REPORTS" = true ]; then
            clean_reports
        fi
        
        if [ "$CLEAN_BUILD" = true ]; then
            clean_build
        fi
    fi
    
    # Show disk usage after cleanup
    show_disk_usage_after
    
    success "Cleanup completed successfully!"
}

# Run main function
main "$@"
