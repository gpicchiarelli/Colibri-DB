#!/bin/bash

# Script per correggere tutti i riferimenti a Colibr in Colibr (senza ì)

echo "🔧 Correggendo tutti i riferimenti a Colibr in Colibr..."

# Funzione per correggere un file
fix_file() {
    local file="$1"
    if [ -f "$file" ]; then
        # Sostituisce Colibr con Colibr in tutto il file
        sed -i '' 's/Colibr/Colibr/g' "$file"
        echo "✅ Corretto: $file"
    fi
}

# Trova tutti i file che contengono Colibr e li correggi
find . -type f \( -name "*.md" -o -name "*.swift" -o -name "*.html" -o -name "*.css" -o -name "*.yml" -o -name "*.yaml" -o -name "*.sh" -o -name "*.py" -o -name "*.cff" -o -name "*.txt" \) -exec grep -l "Colibr" {} \; | while read file; do
    fix_file "$file"
done

echo "🎉 Tutti i riferimenti a Colibr sono stati corretti in Colibr!"
