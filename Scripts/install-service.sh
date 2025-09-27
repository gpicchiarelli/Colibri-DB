#!/bin/bash

# ColibrìDB Server Installation Script
# This script installs ColibrìDB as a system service on macOS

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
SERVICE_NAME="com.colibridb.server"
SERVICE_USER="_colibridb"
SERVICE_GROUP="_colibridb"
INSTALL_DIR="/usr/local/bin"
DATA_DIR="/var/lib/colibridb"
LOG_DIR="/var/log/colibridb"
PLIST_FILE="/Library/LaunchDaemons/${SERVICE_NAME}.plist"

# Function to print colored output
print_status() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Function to check if running as root
check_root() {
    if [[ $EUID -ne 0 ]]; then
        print_error "This script must be run as root (use sudo)"
        exit 1
    fi
}

# Function to check if service is running
is_service_running() {
    launchctl list | grep -q "$SERVICE_NAME"
}

# Function to stop service
stop_service() {
    if is_service_running; then
        print_status "Stopping ColibrìDB service..."
        launchctl unload "$PLIST_FILE" 2>/dev/null || true
        print_success "Service stopped"
    fi
}

# Function to create service user
create_service_user() {
    print_status "Creating service user and group..."
    
    # Create group if it doesn't exist
    if ! dscl . -read /Groups/$SERVICE_GROUP >/dev/null 2>&1; then
        dscl . -create /Groups/$SERVICE_GROUP
        dscl . -create /Groups/$SERVICE_GROUP PrimaryGroupID 200
        dscl . -create /Groups/$SERVICE_GROUP RealName "ColibrìDB Server"
        print_success "Group $SERVICE_GROUP created"
    else
        print_warning "Group $SERVICE_GROUP already exists"
    fi
    
    # Create user if it doesn't exist
    if ! dscl . -read /Users/$SERVICE_USER >/dev/null 2>&1; then
        dscl . -create /Users/$SERVICE_USER
        dscl . -create /Users/$SERVICE_USER UniqueID 200
        dscl . -create /Users/$SERVICE_USER PrimaryGroupID 200
        dscl . -create /Users/$SERVICE_USER UserShell /usr/bin/false
        dscl . -create /Users/$SERVICE_USER RealName "ColibrìDB Server"
        dscl . -create /Users/$SERVICE_USER NFSHomeDirectory "$DATA_DIR"
        print_success "User $SERVICE_USER created"
    else
        print_warning "User $SERVICE_USER already exists"
    fi
}

# Function to create directories
create_directories() {
    print_status "Creating directories..."
    
    # Create data directory
    mkdir -p "$DATA_DIR"
    chown "$SERVICE_USER:$SERVICE_GROUP" "$DATA_DIR"
    chmod 755 "$DATA_DIR"
    print_success "Data directory created: $DATA_DIR"
    
    # Create log directory
    mkdir -p "$LOG_DIR"
    chown "$SERVICE_USER:$SERVICE_GROUP" "$LOG_DIR"
    chmod 755 "$LOG_DIR"
    print_success "Log directory created: $LOG_DIR"
    
    # Create log files
    touch "$LOG_DIR/server.log"
    touch "$LOG_DIR/server.error.log"
    chown "$SERVICE_USER:$SERVICE_GROUP" "$LOG_DIR"/*.log
    chmod 644 "$LOG_DIR"/*.log
    print_success "Log files created"
}

# Function to install binary
install_binary() {
    print_status "Installing ColibrìDB server binary..."
    
    # Check if binary exists
    if [[ ! -f "./colibri-server" ]]; then
        print_error "ColibrìDB server binary not found. Please build the project first."
        exit 1
    fi
    
    # Copy binary
    cp "./colibri-server" "$INSTALL_DIR/"
    chmod +x "$INSTALL_DIR/colibri-server"
    chown root:wheel "$INSTALL_DIR/colibri-server"
    print_success "Binary installed to $INSTALL_DIR/colibri-server"
}

# Function to install plist
install_plist() {
    print_status "Installing service configuration..."
    
    # Check if plist exists
    if [[ ! -f "./Resources/com.colibridb.server.plist" ]]; then
        print_error "Service plist file not found."
        exit 1
    fi
    
    # Copy plist
    cp "./Resources/com.colibridb.server.plist" "$PLIST_FILE"
    chmod 644 "$PLIST_FILE"
    chown root:wheel "$PLIST_FILE"
    print_success "Service configuration installed"
}

# Function to start service
start_service() {
    print_status "Starting ColibrìDB service..."
    
    # Load service
    launchctl load "$PLIST_FILE"
    
    # Wait a moment for service to start
    sleep 2
    
    # Check if service is running
    if is_service_running; then
        print_success "ColibrìDB service started successfully"
        print_status "Service is running on port 8080"
        print_status "Health check: curl http://localhost:8080/health"
    else
        print_error "Failed to start ColibrìDB service"
        print_status "Check logs: tail -f $LOG_DIR/server.error.log"
        exit 1
    fi
}

# Function to show service status
show_status() {
    print_status "ColibrìDB Service Status:"
    echo "================================"
    
    if is_service_running; then
        print_success "Service is running"
        echo "PID: $(launchctl list | grep "$SERVICE_NAME" | awk '{print $1}')"
        echo "Status: $(launchctl list | grep "$SERVICE_NAME" | awk '{print $2}')"
    else
        print_error "Service is not running"
    fi
    
    echo ""
    echo "Configuration:"
    echo "  Service Name: $SERVICE_NAME"
    echo "  User: $SERVICE_USER"
    echo "  Data Directory: $DATA_DIR"
    echo "  Log Directory: $LOG_DIR"
    echo "  Plist File: $PLIST_FILE"
    echo ""
    echo "Useful commands:"
    echo "  sudo launchctl list | grep colibridb"
    echo "  sudo launchctl unload $PLIST_FILE"
    echo "  sudo launchctl load $PLIST_FILE"
    echo "  tail -f $LOG_DIR/server.log"
    echo "  curl http://localhost:8080/health"
}

# Function to uninstall service
uninstall_service() {
    print_status "Uninstalling ColibrìDB service..."
    
    # Stop service
    stop_service
    
    # Remove plist
    if [[ -f "$PLIST_FILE" ]]; then
        rm -f "$PLIST_FILE"
        print_success "Service configuration removed"
    fi
    
    # Remove binary
    if [[ -f "$INSTALL_DIR/colibri-server" ]]; then
        rm -f "$INSTALL_DIR/colibri-server"
        print_success "Binary removed"
    fi
    
    # Remove user and group
    if dscl . -read /Users/$SERVICE_USER >/dev/null 2>&1; then
        dscl . -delete /Users/$SERVICE_USER
        print_success "User $SERVICE_USER removed"
    fi
    
    if dscl . -read /Groups/$SERVICE_GROUP >/dev/null 2>&1; then
        dscl . -delete /Groups/$SERVICE_GROUP
        print_success "Group $SERVICE_GROUP removed"
    fi
    
    # Ask about data directory
    if [[ -d "$DATA_DIR" ]]; then
        read -p "Remove data directory $DATA_DIR? (y/N): " -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            rm -rf "$DATA_DIR"
            print_success "Data directory removed"
        else
            print_warning "Data directory preserved: $DATA_DIR"
        fi
    fi
    
    # Ask about log directory
    if [[ -d "$LOG_DIR" ]]; then
        read -p "Remove log directory $LOG_DIR? (y/N): " -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            rm -rf "$LOG_DIR"
            print_success "Log directory removed"
        else
            print_warning "Log directory preserved: $LOG_DIR"
        fi
    fi
    
    print_success "ColibrìDB service uninstalled"
}

# Main function
main() {
    echo "ColibrìDB Server Installation Script"
    echo "===================================="
    echo ""
    
    # Check if running as root
    check_root
    
    # Parse command line arguments
    case "${1:-install}" in
        "install")
            print_status "Installing ColibrìDB service..."
            create_service_user
            create_directories
            install_binary
            install_plist
            start_service
            show_status
            ;;
        "uninstall")
            uninstall_service
            ;;
        "status")
            show_status
            ;;
        "start")
            if is_service_running; then
                print_warning "Service is already running"
            else
                start_service
            fi
            ;;
        "stop")
            stop_service
            ;;
        "restart")
            stop_service
            sleep 2
            start_service
            ;;
        "help"|"-h"|"--help")
            echo "Usage: $0 [command]"
            echo ""
            echo "Commands:"
            echo "  install    Install ColibrìDB service (default)"
            echo "  uninstall  Uninstall ColibrìDB service"
            echo "  status     Show service status"
            echo "  start      Start the service"
            echo "  stop       Stop the service"
            echo "  restart    Restart the service"
            echo "  help       Show this help message"
            ;;
        *)
            print_error "Unknown command: $1"
            echo "Use '$0 help' for usage information"
            exit 1
            ;;
    esac
}

# Run main function
main "$@"
