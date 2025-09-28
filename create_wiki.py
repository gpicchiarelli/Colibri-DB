#!/usr/bin/env python3
"""
Script per creare la wiki su GitHub usando l'API REST
"""
import os
import requests
import json
from pathlib import Path

# Configurazione
REPO_OWNER = "gpicchiarelli"
REPO_NAME = "Colibr-DB"
WIKI_DIR = "docs/wiki"
GITHUB_TOKEN = os.getenv("GITHUB_TOKEN")

def get_github_token():
    """Ottieni il token GitHub da gh CLI"""
    import subprocess
    try:
        result = subprocess.run(['gh', 'auth', 'token'], capture_output=True, text=True)
        if result.returncode == 0:
            return result.stdout.strip()
    except:
        pass
    return None

def create_wiki_page(title, content):
    """Crea una pagina della wiki su GitHub"""
    if not GITHUB_TOKEN:
        print("❌ Token GitHub non trovato. Esegui: gh auth login")
        return False
    
    # URL per creare/aggiornare pagina wiki
    url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/wiki/pages/{title}"
    
    headers = {
        "Authorization": f"token {GITHUB_TOKEN}",
        "Accept": "application/vnd.github.v3+json",
        "User-Agent": "ColibrDB-Wiki-Script"
    }
    
    data = {
        "title": title,
        "body": content
    }
    
    try:
        response = requests.put(url, headers=headers, json=data)
        
        if response.status_code in [200, 201]:
            print(f"✅ Pagina '{title}' creata/aggiornata con successo")
            return True
        else:
            print(f"❌ Errore creando pagina '{title}': {response.status_code}")
            print(f"Response: {response.text}")
            return False
            
    except Exception as e:
        print(f"❌ Errore nella richiesta per '{title}': {e}")
        return False

def main():
    print("🚀 Creazione wiki ColibrDB su GitHub...")
    
    # Ottieni token GitHub
    global GITHUB_TOKEN
    GITHUB_TOKEN = get_github_token()
    
    if not GITHUB_TOKEN:
        print("❌ Impossibile ottenere token GitHub")
        return
    
    # Lista delle pagine da creare
    pages = [
        "Home",
        "Quick-Start", 
        "Architecture",
        "Configuration",
        "CLI-Reference",
        "API-Reference",
        "Development",
        "Troubleshooting",
        "Performance",
        "Examples"
    ]
    
    success_count = 0
    
    for page in pages:
        file_path = Path(WIKI_DIR) / f"{page}.md"
        
        if not file_path.exists():
            print(f"❌ File non trovato: {file_path}")
            continue
        
        print(f"📝 Creando pagina: {page}")
        
        try:
            content = file_path.read_text(encoding='utf-8')
            if create_wiki_page(page, content):
                success_count += 1
        except Exception as e:
            print(f"❌ Errore leggendo file {file_path}: {e}")
    
    print(f"\n🎉 Completato! {success_count}/{len(pages)} pagine create/aggiornate")
    print(f"🔗 Visita: https://github.com/{REPO_OWNER}/{REPO_NAME}/wiki")

if __name__ == "__main__":
    main()
