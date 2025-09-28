#!/bin/bash

# Script per creare la wiki su GitHub usando curl
set -e

REPO_OWNER="gpicchiarelli"
REPO_NAME="Colibr-DB"
WIKI_DIR="docs/wiki"

echo "🚀 Creazione wiki ColibrDB su GitHub..."

# Ottieni token GitHub
GITHUB_TOKEN=$(gh auth token)
if [ -z "$GITHUB_TOKEN" ]; then
    echo "❌ Token GitHub non trovato. Esegui: gh auth login"
    exit 1
fi

# Funzione per creare una pagina wiki
create_wiki_page() {
    local title="$1"
    local file_path="$2"
    
    echo "📝 Creando pagina: $title"
    
    # Leggi il contenuto del file
    local content=$(cat "$file_path" | sed 's/"/\\"/g' | tr '\n' '\\n')
    
    # Crea/aggiorna la pagina wiki
    local response=$(curl -s -w "%{http_code}" -X PUT \
        -H "Authorization: token $GITHUB_TOKEN" \
        -H "Accept: application/vnd.github.v3+json" \
        -H "Content-Type: application/json" \
        "https://api.github.com/repos/$REPO_OWNER/$REPO_NAME/wiki/pages/$title" \
        -d "{\"title\":\"$title\",\"body\":\"$content\"}")
    
    local http_code="${response: -3}"
    local body="${response%???}"
    
    if [ "$http_code" = "200" ] || [ "$http_code" = "201" ]; then
        echo "✅ Pagina '$title' creata/aggiornata con successo"
        return 0
    else
        echo "❌ Errore creando pagina '$title': HTTP $http_code"
        echo "Response: $body"
        return 1
    fi
}

# Lista delle pagine da creare
pages=(
    "Home"
    "Quick-Start" 
    "Architecture"
    "Configuration"
    "CLI-Reference"
    "API-Reference"
    "Development"
    "Troubleshooting"
    "Performance"
    "Examples"
)

success_count=0
total_count=${#pages[@]}

for page in "${pages[@]}"; do
    file_path="$WIKI_DIR/${page}.md"
    
    if [ ! -f "$file_path" ]; then
        echo "❌ File non trovato: $file_path"
        continue
    fi
    
    if create_wiki_page "$page" "$file_path"; then
        ((success_count++))
    fi
    
    echo ""  # Riga vuota per leggibilità
done

echo "🎉 Completato! $success_count/$total_count pagine create/aggiornate"
echo "🔗 Visita: https://github.com/$REPO_OWNER/$REPO_NAME/wiki"
