#!/bin/bash

# Script per testare i link del sito

echo "🔗 Testando i link del sito ColibrDB..."

# Base URL del sito
BASE_URL="https://gpicchiarelli.github.io/Colibri-DB"

# Lista dei link da testare
LINKS=(
    "/"
    "/wiki/Quick-Start"
    "/wiki/Architecture"
    "/wiki/CLI-Reference"
    "/wiki/API-Reference"
    "/wiki/Configuration"
    "/wiki/Development"
    "/wiki/Performance"
    "/wiki/Troubleshooting"
    "/wiki/Examples"
    "/wiki/Home"
    "/docs/Part-01-Foundations/00-Guida-Alla-Lettura"
    "/docs/Part-02-Core-Engine/00-Introduzione"
    "/docs/Part-03-Query/00-Introduzione"
    "/docs/Part-04-Metadata/00-Introduzione"
    "/docs/Part-05-Server/00-Introduzione"
    "/docs/Part-06-Tooling/00-Introduzione"
)

# Funzione per testare un link
test_link() {
    local url="$1"
    local full_url="${BASE_URL}${url}"
    
    echo -n "Testing ${url}... "
    
    # Usa curl per testare il link
    if curl -s -o /dev/null -w "%{http_code}" "$full_url" | grep -q "200"; then
        echo "✅ OK"
        return 0
    else
        echo "❌ FAIL"
        return 1
    fi
}

# Testa tutti i link
failed_links=()
for link in "${LINKS[@]}"; do
    if ! test_link "$link"; then
        failed_links+=("$link")
    fi
done

# Risultato finale
echo ""
echo "📊 Risultati del test:"
echo "✅ Link funzionanti: $((${#LINKS[@]} - ${#failed_links[@]}))"
echo "❌ Link falliti: ${#failed_links[@]}"

if [ ${#failed_links[@]} -gt 0 ]; then
    echo ""
    echo "🔧 Link che necessitano correzione:"
    for link in "${failed_links[@]}"; do
        echo "  - $link"
    done
else
    echo ""
    echo "🎉 Tutti i link funzionano correttamente!"
fi
