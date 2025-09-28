#!/bin/bash

# Script per correggere tutti i riferimenti a Colibrì in Colibr (senza ì)

echo "🔧 Correggendo tutti i riferimenti a Colibrì in Colibr..."

# Funzione per correggere un file
fix_file() {
    local file="$1"
    if [ -f "$file" ]; then
        # Sostituisce Colibrì con Colibr in tutto il file
        sed -i '' 's/Colibrì/Colibr/g' "$file"
        echo "✅ Corretto: $file"
    fi
}

# Trova tutti i file che contengono Colibrì e li correggi
find . -type f \( -name "*.md" -o -name "*.swift" -o -name "*.html" -o -name "*.css" -o -name "*.yml" -o -name "*.yaml" -o -name "*.sh" -o -name "*.py" -o -name "*.cff" -o -name "*.txt" \) -exec grep -l "Colibrì" {} \; | while read file; do
    fix_file "$file"
done

echo "🎉 Tutti i riferimenti a Colibrì sono stati corretti in Colibr!"
