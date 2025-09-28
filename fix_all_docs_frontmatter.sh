#!/bin/bash

# Script completo per aggiungere front matter Jekyll a tutti i file della documentazione

echo "🔧 Aggiungendo front matter Jekyll a tutti i file della documentazione..."

# Funzione per aggiungere front matter a un file
add_frontmatter() {
    local file="$1"
    local title="$2"
    local description="$3"
    
    # Crea un file temporaneo con il front matter
    cat > "${file}.tmp" << EOF
---
layout: page
title: $title
description: $description
---

EOF
    
    # Aggiungi il contenuto originale
    cat "$file" >> "${file}.tmp"
    
    # Sostituisci il file originale
    mv "${file}.tmp" "$file"
    
    echo "✅ Aggiunto front matter a: $file"
}

# Parte I - Fondamenti
add_frontmatter "docs/Part-01-Foundations/01-Relational-Principles.md" "Principi Relazionali" "Capitolo 1 - Principi del modello relazionale"
add_frontmatter "docs/Part-01-Foundations/02-Algebra-SQL.md" "Algebra SQL" "Capitolo 2 - Algebra relazionale e SQL"
add_frontmatter "docs/Part-01-Foundations/03-Transactions-Theory.md" "Teoria delle Transazioni" "Capitolo 3 - Teoria delle transazioni e ACID"
add_frontmatter "docs/Part-01-Foundations/04-Storage-Principles.md" "Principi di Storage" "Capitolo 4 - Principi di storage e persistenza"

# Parte III - Query
add_frontmatter "docs/Part-03-Query/01-SQL-Parser.md" "SQL Parser" "Capitolo 13 - Parser SQL in ColibrDB"
add_frontmatter "docs/Part-03-Query/02-Logical-Planning.md" "Logical Planning" "Capitolo 14 - Pianificazione logica delle query"
add_frontmatter "docs/Part-03-Query/03-Physical-Planning.md" "Physical Planning" "Capitolo 15 - Pianificazione fisica delle query"
add_frontmatter "docs/Part-03-Query/04-Execution-Engine.md" "Execution Engine" "Capitolo 16 - Motore di esecuzione query"
add_frontmatter "docs/Part-03-Query/05-Advanced-Features.md" "Funzionalità Avanzate" "Capitolo 17 - Funzionalità avanzate delle query"

# Parte IV - Metadati
add_frontmatter "docs/Part-04-Metadata/01-CatalogCore.md" "Catalog Core" "Capitolo 18 - Core del catalogo di sistema"
add_frontmatter "docs/Part-04-Metadata/02-CatalogManager.md" "Catalog Manager" "Capitolo 19 - Gestore del catalogo"
add_frontmatter "docs/Part-04-Metadata/03-Statistics.md" "Statistiche" "Capitolo 20 - Statistiche e ottimizzazione"

# Parte VI - Tooling
add_frontmatter "docs/Part-06-Tooling/01-User-CLI.md" "User CLI" "Capitolo 21 - CLI per utenti"
add_frontmatter "docs/Part-06-Tooling/02-Dev-CLI.md" "Dev CLI" "Capitolo 22 - CLI per sviluppatori"
add_frontmatter "docs/Part-06-Tooling/03-Monitoring-DevOps.md" "Monitoring e DevOps" "Capitolo 23 - Monitoring e operazioni DevOps"

# Parte VII - Testing
add_frontmatter "docs/Part-07-Testing/00-Introduzione.md" "Introduzione al Testing" "Parte VII - Introduzione al testing"
add_frontmatter "docs/Part-07-Testing/01-Unit-Tests.md" "Unit Tests" "Capitolo 24 - Test unitari"
add_frontmatter "docs/Part-07-Testing/02-Integration-Tests.md" "Integration Tests" "Capitolo 25 - Test di integrazione"
add_frontmatter "docs/Part-07-Testing/03-Benchmarks.md" "Benchmarks" "Capitolo 26 - Benchmark e performance"

# Appendici
add_frontmatter "docs/Appendices/00-Introduzione.md" "Introduzione alle Appendici" "Appendici - Introduzione"
add_frontmatter "docs/Appendices/01-Glossario.md" "Glossario" "Appendice A - Glossario dei termini"
add_frontmatter "docs/Appendices/02-Configurazione.md" "Configurazione" "Appendice B - Guida alla configurazione"

# File speciali
add_frontmatter "docs/Prefazione.md" "Prefazione" "Prefazione alla documentazione ColibrDB"
add_frontmatter "docs/README.md" "Documentazione ColibrDB" "Documentazione tecnica completa di ColibrDB"

echo "🎉 Front matter aggiunto a tutti i file della documentazione!"
