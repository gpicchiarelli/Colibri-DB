# ColibriServer — Database Server

The network server component for ColibrìDB, providing client connectivity and request handling.

## Components

### Core Server
- **`Server.swift`** — Main server implementation with connection management
- **`ConnectionManager.swift`** — Connection pooling and transaction management
- **`WireProtocol.swift`** — Network protocol and message handling

## Features

- **Connection Management**: Efficient connection pooling and lifecycle management
- **Request Processing**: SQL query parsing and execution pipeline
- **Security**: TLS support and authentication integration
- **Monitoring**: Built-in metrics and health checks
- **Scalability**: Multi-threaded request handling

## Architecture

The server follows a modular design:

```
Client Request → Wire Protocol → Connection Manager → Query Processor → ColibriCore
```

## Configuration

Server settings can be configured through:
- Command-line arguments
- Configuration file (`colibridb.conf.json`)
- Environment variables

## Usage

```bash
# Start the server
coldb-server --config colibridb.conf.json

# Start with custom port
coldb-server --port 5432 --host 0.0.0.0
```

## Documentation

For detailed information, see:
- **Server Architecture**: `docs/architecture.html`
- **Configuration Guide**: `docs/configuration.html`
- **API Reference**: `docs/api-reference.html`

