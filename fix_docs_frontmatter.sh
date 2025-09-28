#!/bin/bash

# Script per aggiungere front matter Jekyll ai file della documentazione tecnica

echo "🔧 Aggiungendo front matter Jekyll ai file della documentazione..."

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

# File della documentazione tecnica
add_frontmatter "docs/Part-02-Core-Engine/02-BufferPool.md" "Buffer Pool Management" "Capitolo 6 - Gestione del buffer pool in ColibrìDB"
add_frontmatter "docs/Part-02-Core-Engine/03-Heap-Storage.md" "Heap Storage Engine" "Capitolo 7 - Motore di storage heap in ColibrìDB"
add_frontmatter "docs/Part-02-Core-Engine/04-BTree-Indexes.md" "B+Tree Indexes" "Capitolo 8 - Indici B+Tree in ColibrìDB"
add_frontmatter "docs/Part-02-Core-Engine/05-MVCC-Concurrency.md" "MVCC e Concorrenza" "Capitolo 9 - MVCC e controllo concorrenza in ColibrìDB"

add_frontmatter "docs/Part-05-Server/01-ServerArchitecture.md" "Architettura Server" "Capitolo 10 - Architettura del server ColibrìDB"
add_frontmatter "docs/Part-05-Server/02-Wire-Protocol.md" "Wire Protocol" "Capitolo 11 - Protocollo di comunicazione ColibrìDB"
add_frontmatter "docs/Part-05-Server/03-ServerOperations.md" "Operazioni Server" "Capitolo 12 - Operazioni del server ColibrìDB"

add_frontmatter "docs/Part-08-Future/00-Introduzione.md" "Introduzione al Futuro" "Parte VIII - Introduzione alle funzionalità future"
add_frontmatter "docs/Part-08-Future/01-Roadmap.md" "Roadmap del Progetto" "Roadmap e piani futuri per ColibrìDB"

echo "🎉 Front matter aggiunto a tutti i file della documentazione tecnica!"
