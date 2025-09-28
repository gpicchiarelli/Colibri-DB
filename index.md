---
layout: default
title: ColibrìDB
description: Un RDBMS sperimentale ad alte prestazioni scritto in Swift 6.2
---

<!-- Overview Section -->
<section id="overview" class="section">
    <h2>🎯 Panoramica</h2>
    <p><strong>ColibrìDB</strong> è un RDBMS sperimentale scritto in Swift 6.2 pensato per gestire milioni di connessioni logiche, ottimizzato per macOS e Apple Silicon. Il progetto punta a un'architettura modulare: motore heap su disco con WAL, MVCC, indici pluggabili e CLI amministrativa <code>coldb</code>.</p>
</section>

<!-- Features Section -->
<section id="features" class="section">
    <h2>✨ Caratteristiche Principali</h2>
    <div class="features-grid">
        <div class="feature-card">
            <h4>🗄️ Storage & Buffering</h4>
            <ul>
                <li>Heap File Storage con slot directory</li>
                <li>Compattazione Online in tempo reale</li>
                <li>Buffer Pool LRU/Clock intelligente</li>
                <li>Ottimizzato Apple Silicon ARM64</li>
            </ul>
        </div>
        <div class="feature-card">
            <h4>🔒 Durabilità Enterprise</h4>
            <ul>
                <li>WAL v2 con checksum CRC32</li>
                <li>Recovery ARIES-compliant</li>
                <li>Transaction Logging UNDO/REDO</li>
                <li>Index Recovery da WAL</li>
            </ul>
        </div>
        <div class="feature-card">
            <h4>🚀 Indicizzazione Avanzata</h4>
            <ul>
                <li>B+Tree Persistente su disco</li>
                <li>Tipi pluggabili: Hash, ART, LSM</li>
                <li>Validazione profonda integrità</li>
                <li>Memory-Efficient per dataset grandi</li>
            </ul>
        </div>
        <div class="feature-card">
            <h4>⚡ Controllo Concorrenza</h4>
            <ul>
                <li>MVCC Multi-Version Control</li>
                <li>Lock Manager con deadlock detection</li>
                <li>Supporto Two-Phase Commit</li>
                <li>Snapshot Isolation per query complesse</li>
            </ul>
        </div>
        <div class="feature-card">
            <h4>🧠 Elaborazione Query</h4>
            <ul>
                <li>Volcano Iterator cost-based</li>
                <li>Operatori avanzati: Scan, Filter, Join</li>
                <li>Viste Materializzate cached</li>
                <li>SQL Parser compatibilità completa</li>
            </ul>
        </div>
        <div class="feature-card">
            <h4>🛠️ Operazioni</h4>
            <ul>
                <li>CLI Amministrativa completa</li>
                <li>Import/Export CSV bulk</li>
                <li>Metriche Prometheus integrate</li>
                <li>Policy Engine automatizzato</li>
            </ul>
        </div>
    </div>
</section>

<!-- Quick Start Section -->
<section id="quick-start" class="section">
    <h2>🚀 Quick Start</h2>
    <div class="quick-start">
        <h3>Prerequisiti</h3>
        <ul>
            <li><strong>macOS 13+</strong> (Apple Silicon consigliato per performance ottimali)</li>
            <li><strong>Swift 6.2</strong> (o toolchain compatibile via SwiftPM)</li>
            <li><strong>Spazio su disco</strong>: Sufficiente per dati (<code>data/</code>), WAL e indici</li>
        </ul>

        <div class="step">
            <h4>1. Installazione</h4>
            <div class="code-block">
                <pre># Clona il repository
git clone https://github.com/gpicchiarelli/Colibr-DB.git
cd Colibr-DB

# Compila il progetto
swift build

# Esegui la CLI
.build/debug/coldb --config colibridb.conf.json</pre>
            </div>
        </div>

        <div class="step">
            <h4>2. Prima Sessione</h4>
            <div class="code-block">
                <pre># Avvia una sessione interattiva
.build/debug/coldb

# Crea una tabella
\create table demo

# Inserisci dati
\insert demo id=1,name=Alice,age=25

# Crea un indice
\create index idx_demo_name ON demo(name) USING BTree

# Interroga i dati
\select * FROM demo WHERE name = 'Alice'</pre>
            </div>
        </div>
    </div>
</section>

<!-- Documentation Section -->
<section id="documentation" class="section">
    <h2>📚 Documentazione Completa</h2>
    <p>La documentazione è organizzata in sezioni progressive per diversi livelli di competenza:</p>
    
    <div class="features-grid">
        <div class="feature-card">
            <h4>🚀 Wiki Operativa</h4>
            <ul>
                <li><a href="{{ site.baseurl }}/wiki/Quick-Start">Quick Start</a> - Installazione e prima sessione</li>
                <li><a href="{{ site.baseurl }}/wiki/Architecture">Architecture</a> - Architettura del sistema</li>
                <li><a href="{{ site.baseurl }}/wiki/CLI-Reference">CLI Reference</a> - Comandi completi</li>
                <li><a href="{{ site.baseurl }}/wiki/API-Reference">API Reference</a> - Documentazione API</li>
                <li><a href="{{ site.baseurl }}/wiki/Performance">Performance</a> - Ottimizzazioni e benchmark</li>
                <li><a href="{{ site.baseurl }}/wiki/Troubleshooting">Troubleshooting</a> - Risoluzione problemi</li>
                <li><a href="{{ site.baseurl }}/wiki/Examples">Examples</a> - Esempi pratici</li>
            </ul>
        </div>
        <div class="feature-card">
            <h4>🎓 Manuale Tecnico</h4>
            <ul>
                <li><a href="{{ site.baseurl }}/docs/Part-01-Foundations/00-Guida-Alla-Lettura">Parte I: Fondamenti</a> - Principi relazionali, algebra SQL</li>
                <li><a href="{{ site.baseurl }}/docs/Part-02-Core-Engine/00-Introduzione">Parte II: Motore Core</a> - WAL, Buffer Pool, Indici</li>
                <li><a href="{{ site.baseurl }}/docs/Part-03-Query/00-Introduzione">Parte III: Elaborazione Query</a> - Parser, Planning, Execution</li>
                <li><a href="{{ site.baseurl }}/docs/Part-04-Metadata/00-Introduzione">Parte IV: Metadati</a> - Catalog, Statistiche</li>
                <li><a href="{{ site.baseurl }}/docs/Part-05-Server/00-Introduzione">Parte V: Server</a> - Architettura, Wire Protocol</li>
                <li><a href="{{ site.baseurl }}/docs/Part-06-Tooling/00-Introduzione">Parte VI: Strumenti</a> - CLI, Monitoring</li>
            </ul>
        </div>
    </div>
</section>

<!-- Architecture Section -->
<section id="architecture" class="section">
    <h2>🏗️ Architettura del Sistema</h2>
    <p>ColibrìDB è progettato con un'architettura modulare che separa chiaramente le responsabilità:</p>
    
    <div class="features-grid">
        <div class="feature-card">
            <h4>Storage Engine</h4>
            <p>Storage basato su file heap con slot directory e Free Space Map persistente per gestione efficiente dello spazio.</p>
        </div>
        <div class="feature-card">
            <h4>Buffer Pool</h4>
            <p>Eviction LRU/Clock con flush in background e quote per namespace per ottimizzazione memoria.</p>
        </div>
        <div class="feature-card">
            <h4>Sistema WAL</h4>
            <p>Recovery ARIES-compliant con checksum CRC32 per garantire durabilità e consistenza dei dati.</p>
        </div>
        <div class="feature-card">
            <h4>Motore Indici</h4>
            <p>Implementazioni pluggabili B+Tree, Hash, ART e LSM per diverse esigenze di accesso ai dati.</p>
        </div>
    </div>
</section>

<!-- Contributing Section -->
<section id="contributing" class="section">
    <h2>🤝 Contribuire</h2>
    <p>Accogliamo i contributi! Consulta le nostre <a href="https://github.com/gpicchiarelli/Colibr-DB/blob/main/CONTRIBUTING.md">Linee Guida per i Contributi</a> e il <a href="https://github.com/gpicchiarelli/Colibr-DB/blob/main/CODE_OF_CONDUCT.md">Codice di Condotta</a> per i dettagli.</p>
    
    <div class="features-grid">
        <div class="feature-card">
            <h4>🔧 Aree per i Contributi</h4>
            <ul>
                <li>Motore Core: Storage, WAL, indicizzazione</li>
                <li>Elaborazione Query: Parser, ottimizzazione</li>
                <li>Testing: Copertura test, benchmark</li>
                <li>Documentazione: Scrittura tecnica, esempi</li>
            </ul>
        </div>
        <div class="feature-card">
            <h4>📈 Roadmap</h4>
            <ul>
                <li>✅ MVP (Alpha): Motore core, WAL, indici</li>
                <li>🔄 Release Beta: Server multi-utente</li>
                <li>🚀 Release Produzione: SQL completo</li>
                <li>🌐 Futuro: Architettura distribuita</li>
            </ul>
        </div>
    </div>
</section>
