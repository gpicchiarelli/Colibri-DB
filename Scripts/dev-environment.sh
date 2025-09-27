#!/bin/bash

# ColibrìDB Development Environment Setup Script
# This script sets up a complete development and testing environment

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEV_DIR="$PROJECT_ROOT/dev-environment"
LOGS_DIR="$DEV_DIR/logs"
DATA_DIR="$DEV_DIR/data"
TESTS_DIR="$DEV_DIR/tests"
REPORTS_DIR="$DEV_DIR/reports"
CONFIGS_DIR="$DEV_DIR/configs"

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

# Main functions
setup_directories() {
    log "Setting up development directories..."
    
    mkdir -p "$DEV_DIR"
    mkdir -p "$LOGS_DIR"
    mkdir -p "$DATA_DIR"
    mkdir -p "$TESTS_DIR"
    mkdir -p "$REPORTS_DIR"
    mkdir -p "$CONFIGS_DIR"
    
    # Create subdirectories
    mkdir -p "$LOGS_DIR/server"
    mkdir -p "$LOGS_DIR/cli"
    mkdir -p "$LOGS_DIR/tests"
    mkdir -p "$LOGS_DIR/benchmarks"
    mkdir -p "$LOGS_DIR/telemetry"
    
    mkdir -p "$DATA_DIR/databases"
    mkdir -p "$DATA_DIR/backups"
    mkdir -p "$DATA_DIR/temp"
    
    mkdir -p "$TESTS_DIR/unit"
    mkdir -p "$TESTS_DIR/integration"
    mkdir -p "$TESTS_DIR/performance"
    mkdir -p "$TESTS_DIR/stress"
    mkdir -p "$TESTS_DIR/regression"
    
    mkdir -p "$REPORTS_DIR/test-results"
    mkdir -p "$REPORTS_DIR/benchmarks"
    mkdir -p "$REPORTS_DIR/telemetry"
    mkdir -p "$REPORTS_DIR/coverage"
    
    success "Directories created"
}

setup_configurations() {
    log "Setting up development configurations..."
    
    # Development configuration
    cat > "$CONFIGS_DIR/colibridb-dev.conf.json" << 'EOF'
{
  "dataDir": "./dev-environment/data",
  "maxConnectionsLogical": 1000,
  "maxConnectionsPhysical": 8,
  "bufferPoolSizeBytes": 268435456,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true,
  "serverEnabled": true,
  "serverHost": "localhost",
  "serverPort": 8080,
  "indexImplementation": "Hash",
  "storageEngine": "FileHeap",
  "logLevel": "debug",
  "telemetryEnabled": true,
  "profilingEnabled": true,
  "debugMode": true
}
EOF

    # Testing configuration
    cat > "$CONFIGS_DIR/colibridb-test.conf.json" << 'EOF'
{
  "dataDir": "./dev-environment/data/test",
  "maxConnectionsLogical": 100,
  "maxConnectionsPhysical": 4,
  "bufferPoolSizeBytes": 67108864,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true,
  "serverEnabled": false,
  "indexImplementation": "Hash",
  "storageEngine": "FileHeap",
  "logLevel": "info",
  "telemetryEnabled": true,
  "profilingEnabled": false,
  "debugMode": false
}
EOF

    # Performance testing configuration
    cat > "$CONFIGS_DIR/colibridb-perf.conf.json" << 'EOF'
{
  "dataDir": "./dev-environment/data/perf",
  "maxConnectionsLogical": 10000,
  "maxConnectionsPhysical": 16,
  "bufferPoolSizeBytes": 1073741824,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true,
  "serverEnabled": true,
  "serverHost": "localhost",
  "serverPort": 8081,
  "indexImplementation": "ART",
  "storageEngine": "FileHeap",
  "logLevel": "warn",
  "telemetryEnabled": true,
  "profilingEnabled": true,
  "debugMode": false
}
EOF

    success "Configurations created"
}

build_project() {
    log "Building ColibrìDB project..."
    
    cd "$PROJECT_ROOT"
    
    # Clean previous build
    swift package clean
    
    # Build in release mode
    swift build --configuration release
    
    success "Project built successfully"
}

setup_test_data() {
    log "Setting up test data..."
    
    # Create sample databases for testing
    cat > "$TESTS_DIR/test-data.sql" << 'EOF'
-- Test database setup
CREATE DATABASE test_db;
USE test_db;

-- Users table
CREATE TABLE users (
    id INTEGER PRIMARY KEY,
    name VARCHAR(100) NOT NULL,
    email VARCHAR(255) UNIQUE NOT NULL,
    age INTEGER CHECK (age >= 0 AND age <= 150),
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    is_active BOOLEAN DEFAULT TRUE
);

-- Products table
CREATE TABLE products (
    id INTEGER PRIMARY KEY,
    name VARCHAR(200) NOT NULL,
    description TEXT,
    price DECIMAL(10,2) CHECK (price >= 0),
    category_id INTEGER,
    stock_quantity INTEGER DEFAULT 0 CHECK (stock_quantity >= 0),
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Orders table
CREATE TABLE orders (
    id INTEGER PRIMARY KEY,
    user_id INTEGER,
    product_id INTEGER,
    quantity INTEGER CHECK (quantity > 0),
    total_price DECIMAL(10,2),
    order_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    status VARCHAR(20) DEFAULT 'pending' CHECK (status IN ('pending', 'processing', 'shipped', 'delivered', 'cancelled'))
);

-- Categories table
CREATE TABLE categories (
    id INTEGER PRIMARY KEY,
    name VARCHAR(100) NOT NULL,
    description TEXT,
    parent_id INTEGER
);

-- Insert test data
INSERT INTO users (id, name, email, age) VALUES 
(1, 'Alice Johnson', 'alice@example.com', 28),
(2, 'Bob Smith', 'bob@example.com', 35),
(3, 'Charlie Brown', 'charlie@example.com', 42),
(4, 'Diana Prince', 'diana@example.com', 30),
(5, 'Eve Wilson', 'eve@example.com', 25);

INSERT INTO categories (id, name, description) VALUES
(1, 'Electronics', 'Electronic devices and accessories'),
(2, 'Clothing', 'Apparel and fashion items'),
(3, 'Books', 'Books and educational materials'),
(4, 'Home & Garden', 'Home improvement and garden supplies');

INSERT INTO products (id, name, description, price, category_id, stock_quantity) VALUES
(1, 'Laptop Pro', 'High-performance laptop', 1299.99, 1, 50),
(2, 'Wireless Mouse', 'Ergonomic wireless mouse', 29.99, 1, 200),
(3, 'Cotton T-Shirt', 'Comfortable cotton t-shirt', 19.99, 2, 100),
(4, 'Programming Book', 'Learn Swift programming', 49.99, 3, 75),
(5, 'Garden Tools Set', 'Complete garden tools set', 89.99, 4, 25);

INSERT INTO orders (id, user_id, product_id, quantity, total_price, status) VALUES
(1, 1, 1, 1, 1299.99, 'delivered'),
(2, 2, 2, 2, 59.98, 'shipped'),
(3, 3, 3, 3, 59.97, 'processing'),
(4, 4, 4, 1, 49.99, 'pending'),
(5, 5, 5, 1, 89.99, 'delivered');

-- Create indexes
CREATE INDEX idx_users_email ON users(email);
CREATE INDEX idx_products_category ON products(category_id);
CREATE INDEX idx_orders_user ON orders(user_id);
CREATE INDEX idx_orders_product ON orders(product_id);
CREATE INDEX idx_orders_date ON orders(order_date);
EOF

    success "Test data created"
}

setup_telemetry() {
    log "Setting up telemetry system..."
    
    # Create telemetry configuration
    cat > "$CONFIGS_DIR/telemetry.conf.json" << 'EOF'
{
  "enabled": true,
  "logLevel": "debug",
  "metricsInterval": 1.0,
  "profilingEnabled": true,
  "memoryTracking": true,
  "performanceTracking": true,
  "queryTracking": true,
  "transactionTracking": true,
  "indexTracking": true,
  "ioTracking": true,
  "errorTracking": true,
  "exportFormats": ["json", "prometheus", "csv"],
  "exportInterval": 60.0,
  "retentionDays": 30,
  "compressionEnabled": true
}
EOF

    success "Telemetry system configured"
}

create_development_scripts() {
    log "Creating development scripts..."
    
    # Main development script
    cat > "$DEV_DIR/dev-loop.sh" << 'EOF'
#!/bin/bash

# ColibrìDB Development Loop Script
# This script runs the complete development and testing cycle

set -e

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEV_DIR="$PROJECT_ROOT/dev-environment"

# Colors
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log() {
    echo -e "${BLUE}[$(date +'%Y-%m-%d %H:%M:%S')]${NC} $1"
}

success() {
    echo -e "${GREEN}[$(date +'%Y-%m-%d %H:%M:%S')] ✓${NC} $1"
}

error() {
    echo -e "${RED}[$(date +'%Y-%m-%d %H:%M:%S')] ✗${NC} $1"
}

# Function to run complete test cycle
run_test_cycle() {
    local cycle_id="$1"
    local start_time=$(date +%s)
    
    log "Starting test cycle $cycle_id"
    
    # 1. Build project
    log "Building project..."
    cd "$PROJECT_ROOT"
    swift build --configuration release
    
    # 2. Start server
    log "Starting server..."
    .build/release/colibri-server --config "$DEV_DIR/configs/colibridb-dev.conf.json" &
    SERVER_PID=$!
    sleep 5
    
    # 3. Run tests
    log "Running test suite..."
    "$DEV_DIR/scripts/run-tests.sh" --config "$DEV_DIR/configs/colibridb-test.conf.json"
    
    # 4. Run benchmarks
    log "Running benchmarks..."
    "$DEV_DIR/scripts/run-benchmarks.sh" --config "$DEV_DIR/configs/colibridb-perf.conf.json"
    
    # 5. Collect telemetry
    log "Collecting telemetry..."
    "$DEV_DIR/scripts/collect-telemetry.sh" --output "$DEV_DIR/reports/telemetry/cycle-$cycle_id"
    
    # 6. Generate report
    log "Generating report..."
    "$DEV_DIR/scripts/generate-report.sh" --cycle "$cycle_id" --output "$DEV_DIR/reports/test-results/cycle-$cycle_id"
    
    # 7. Stop server
    log "Stopping server..."
    kill $SERVER_PID 2>/dev/null || true
    sleep 2
    
    # 8. Cleanup
    log "Cleaning up..."
    "$DEV_DIR/scripts/cleanup.sh"
    
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    success "Test cycle $cycle_id completed in ${duration}s"
}

# Main execution
if [ "$1" = "--continuous" ]; then
    log "Starting continuous development loop..."
    cycle=1
    while true; do
        run_test_cycle $cycle
        cycle=$((cycle + 1))
        sleep 60  # Wait 1 minute between cycles
    done
else
    run_test_cycle 1
fi
EOF

    chmod +x "$DEV_DIR/dev-loop.sh"
    
    success "Development scripts created"
}

# Main execution
main() {
    log "Setting up ColibrìDB development environment..."
    
    setup_directories
    setup_configurations
    build_project
    setup_test_data
    setup_telemetry
    create_development_scripts
    
    success "Development environment setup complete!"
    log "Environment location: $DEV_DIR"
    log "To start development loop: $DEV_DIR/dev-loop.sh"
    log "To start continuous loop: $DEV_DIR/dev-loop.sh --continuous"
}

# Run main function
main "$@"
