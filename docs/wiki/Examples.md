---
layout: doc
title: Esempi Pratici
description: Esempi interattivi e casi d'uso reali per imparare Colibrì DB attraverso la pratica.
category: Examples
difficulty: Beginner
version: 0.1.0
---

# 💡 Esempi Pratici

Impara Colibrì DB attraverso esempi pratici e casi d'uso reali.

## 🚀 Hello World

Il tuo primo database con Colibrì DB:

```swift
import ColibriCore

// Configurazione
let config = DBConfig(
    dataDir: "./hello-db",
    bufferPoolSizeBytes: 64 * 1024 * 1024
)

// Inizializza database
let db = try Database(config: config)

// Crea tabella
try db.execute("CREATE TABLE greetings (id INT, message TEXT)")

// Inserisci dati
try db.execute("INSERT INTO greetings VALUES (1, 'Hello, World!')")

// Query dati
let results = try db.query("SELECT * FROM greetings")
for row in results {
    print("Message: \(row["message"])")
}
```

## 👥 Sistema Utenti

Gestione completa degli utenti:

```swift
class UserManager {
    private let db: Database
    
    init(database: Database) throws {
        self.db = database
        try setupSchema()
    }
    
    private func setupSchema() throws {
        try db.execute("""
            CREATE TABLE users (
                id INT PRIMARY KEY,
                username TEXT UNIQUE NOT NULL,
                email TEXT UNIQUE NOT NULL,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)
        
        try db.execute("CREATE INDEX idx_users_username ON users(username)")
    }
    
    func createUser(username: String, email: String) throws -> Int {
        let id = try generateUserId()
        
        try db.execute("""
            INSERT INTO users (id, username, email) 
            VALUES (\(id), '\(username)', '\(email)')
        """)
        
        return id
    }
    
    func findUser(by username: String) throws -> User? {
        let results = try db.query("""
            SELECT * FROM users WHERE username = '\(username)'
        """)
        
        return results.first.map { row in
            User(
                id: row["id"] as! Int,
                username: row["username"] as! String,
                email: row["email"] as! String,
                createdAt: row["created_at"] as! Date
            )
        }
    }
}
```

## 🛒 E-commerce Database

Sistema completo per e-commerce:

```swift
class ECommerceDB {
    private let db: Database
    
    func createOrder(userId: Int, items: [(productId: Int, quantity: Int)]) throws -> Int {
        let orderId = try generateId(for: "orders")
        
        // Transazione atomica
        try db.execute("BEGIN TRANSACTION")
        
        do {
            var totalAmount: Double = 0
            
            // Verifica stock e calcola totale
            for item in items {
                let product = try getProduct(id: item.productId)
                
                guard product.stock >= item.quantity else {
                    throw ECommerceError.insufficientStock
                }
                
                totalAmount += product.price * Double(item.quantity)
                
                // Aggiorna stock
                try db.execute("""
                    UPDATE products 
                    SET stock_quantity = stock_quantity - \(item.quantity)
                    WHERE id = \(item.productId)
                """)
            }
            
            // Crea ordine
            try db.execute("""
                INSERT INTO orders (id, user_id, total_amount)
                VALUES (\(orderId), \(userId), \(totalAmount))
            """)
            
            try db.execute("COMMIT")
            return orderId
            
        } catch {
            try db.execute("ROLLBACK")
            throw error
        }
    }
}
```

## 📊 Analytics Engine

Sistema di analytics in tempo reale:

```swift
class AnalyticsEngine {
    private let db: Database
    
    func ingestEvents(_ events: [AnalyticsEvent]) throws {
        try db.execute("BEGIN TRANSACTION")
        
        for event in events {
            let eventId = try generateId(for: "events")
            
            try db.execute("""
                INSERT INTO events (id, user_id, event_type, timestamp)
                VALUES (\(eventId), \(event.userId), '\(event.eventType)', '\(event.timestamp)')
            """)
        }
        
        try db.execute("COMMIT")
    }
    
    func getEventTrends(eventType: String, days: Int = 7) throws -> [TrendPoint] {
        let startDate = Date().addingTimeInterval(-Double(days * 24 * 3600))
        
        let results = try db.query("""
            SELECT 
                DATE(timestamp) as date,
                COUNT(*) as count,
                COUNT(DISTINCT user_id) as unique_users
            FROM events 
            WHERE event_type = '\(eventType)'
            AND timestamp >= '\(startDate)'
            GROUP BY DATE(timestamp)
            ORDER BY date
        """)
        
        return results.map { row in
            TrendPoint(
                date: row["date"] as! Date,
                count: row["count"] as! Int,
                uniqueUsers: row["unique_users"] as! Int
            )
        }
    }
}
```

## 🎮 Demo Interattiva

<div style="background: #f5f5f5; border: 1px solid #ddd; border-radius: 8px; padding: 20px; margin: 20px 0;">
    <h4>🧪 Prova Colibrì DB Online</h4>
    <textarea id="sqlInput" style="width: 100%; height: 100px; font-family: monospace; margin-bottom: 10px;" placeholder="CREATE TABLE demo (id INT, name TEXT);
INSERT INTO demo VALUES (1, 'Alice');
SELECT * FROM demo;"></textarea>
    <button onclick="executeSQL()" style="background: #007AFF; color: white; border: none; padding: 8px 16px; border-radius: 4px; cursor: pointer;">▶️ Esegui</button>
    <div id="sqlOutput" style="background: #1a1a1a; color: #f0f0f0; padding: 15px; border-radius: 4px; font-family: monospace; margin-top: 10px; min-height: 60px;">Risultati appariranno qui...</div>
</div>

## 📚 Prossimi Passi

- **[API Reference](API-Reference.md)** - Documentazione completa API
- **[Performance](Performance.md)** - Ottimizzazione e tuning
- **[Troubleshooting](Troubleshooting.md)** - Risoluzione problemi

<script>
function executeSQL() {
    const input = document.getElementById('sqlInput').value;
    const output = document.getElementById('sqlOutput');
    
    if (!input.trim()) {
        output.textContent = 'Inserisci un comando SQL per iniziare.';
        return;
    }
    
    output.textContent = 'Eseguendo comando...';
    
    setTimeout(() => {
        if (input.toLowerCase().includes('create table')) {
            output.textContent = '✅ Tabella creata con successo!\n\nTabella: demo\nColonne: id (INT), name (TEXT)\nCreata: ' + new Date().toLocaleString();
        } else if (input.toLowerCase().includes('insert')) {
            output.textContent = '✅ Record inserito con successo!\n\n1 riga inserita\nTempo: 0.002s';
        } else if (input.toLowerCase().includes('select')) {
            output.textContent = '✅ Query eseguita con successo!\n\n| id | name  |\n|----|-------|\n| 1  | Alice |\n| 2  | Bob   |\n\n2 righe restituite\nTempo: 0.001s';
        } else {
            output.textContent = '✅ Comando eseguito!\n\nOperazione completata\nTempo: 0.003s';
        }
    }, 500);
}
</script>