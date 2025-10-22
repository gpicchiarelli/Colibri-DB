# Setup Colibrì DB Website

## ✅ Configurazione Completata

Il sito è ora completamente configurato per funzionare con **Jekyll** e **GitHub Pages**.

## 🎯 Cosa è stato fatto

### 1. **Configurazione Jekyll**
- ✅ `_config.yml` ottimizzato per GitHub Pages
- ✅ `Gemfile` con dipendenze corrette
- ✅ Layout HTML con include per head
- ✅ Collections per wiki
- ✅ Defaults per pagine e documentazione

### 2. **Struttura File**
- ✅ `_layouts/default.html` - Layout principale
- ✅ `_layouts/doc.html` - Layout per documentazione
- ✅ `_includes/head.html` - Include per meta tag
- ✅ `assets/css/main.css` - Stili principali
- ✅ `wiki/` - Documentazione wiki
- ✅ Pagine HTML principali

### 3. **Link e Percorsi**
- ✅ Tutti i link usano `relative_url`
- ✅ `baseurl` configurato su `/Colibri-DB`
- ✅ Asset path corretti
- ✅ Navigazione funzionante

### 4. **Design Professionale**
- ✅ Layout moderno e responsive
- ✅ CSS ottimizzato per Jekyll
- ✅ Animazioni e transizioni
- ✅ Icone e elementi grafici

## 🚀 Deploy su GitHub Pages

### Passo 1: Push su GitHub
```bash
git add .
git commit -m "Add Jekyll website configuration"
git push origin main
```

### Passo 2: Abilita GitHub Pages
1. Vai su GitHub → Settings del repository
2. Scorri fino a "Pages"
3. In "Source" seleziona "Deploy from a branch"
4. Scegli branch `main` e folder `/docs`
5. Clicca "Save"

### Passo 3: Verifica
Il sito sarà disponibile su:
**https://gpicchiarelli.github.io/Colibri-DB/**

## 🧪 Test Locale (Opzionale)

```bash
# Installa Ruby e Bundler
gem install bundler

# Vai nella cartella docs
cd docs

# Installa le dipendenze
bundle install

# Avvia il server locale
bundle exec jekyll serve

# Il sito sarà su http://localhost:4000/Colibri-DB/
```

## 📁 Struttura Finale

```
Colibri-DB/
├── docs/                    # Cartella sorgente Jekyll
│   ├── _config.yml         # Configurazione Jekyll
│   ├── _layouts/           # Layout HTML
│   │   ├── default.html    # Layout principale
│   │   └── doc.html        # Layout documentazione
│   ├── _includes/          # Include HTML
│   │   └── head.html       # Meta tag e CSS
│   ├── assets/             # Asset statici
│   │   └── css/
│   │       └── main.css    # Stili principali
│   ├── wiki/               # Documentazione wiki
│   │   ├── Home.md         # Home wiki
│   │   └── Quick-Start.md  # Quick start
│   ├── index.html          # Homepage
│   ├── architecture.html   # Pagina architettura
│   ├── tla-specifications.html # Specifiche TLA+
│   ├── test.html           # Pagina di test
│   ├── Gemfile             # Dipendenze Ruby
│   ├── README.md           # Documentazione
│   ├── DEPLOY.md           # Istruzioni deploy
│   └── .gitignore          # File da ignorare
└── README.md               # Documentazione progetto
```

## 🔧 Configurazione Chiave

### _config.yml
```yaml
title: "Colibrì DB"
description: "RDBMS professionale per macOS"
baseurl: "/Colibri-DB"  # Nome del repository
url: "https://gpicchiarelli.github.io"

# Collections per wiki
collections:
  wiki:
    output: true
    permalink: /wiki/:name/

# Layout di default
defaults:
  - scope:
      path: ""
      type: "pages"
    values:
      layout: "default"
  - scope:
      path: ""
      type: "wiki"
    values:
      layout: "doc"
```

### Link Interni
Tutti i link usano `relative_url`:
```html
<a href="{{ '/architecture.html' | relative_url }}">Architettura</a>
<a href="{{ '/wiki/Home.html' | relative_url }}">Wiki</a>
```

### Asset
```html
<link rel="stylesheet" href="{{ '/assets/css/main.css' | relative_url }}">
```

## 🎨 Design System

- **Colori**: Palette professionale con primary, secondary, accent
- **Tipografia**: Inter per testi, JetBrains Mono per codice
- **Layout**: Grid system responsive
- **Componenti**: Card, bottoni, sezioni modulari
- **Animazioni**: Transizioni fluide e micro-interazioni

## 🐛 Troubleshooting

### Se il sito non funziona:

1. **Verifica il baseurl**: Deve essere `/Colibri-DB`
2. **Controlla i link**: Devono usare `| relative_url`
3. **Verifica la struttura**: File nella cartella `docs/`
4. **Controlla GitHub Pages**: Abilitato e configurato correttamente

### Debug locale:
```bash
bundle exec jekyll serve --verbose --trace
```

## 🎉 Risultato

Il sito è ora **completamente professionale** e pronto per GitHub Pages:

- ✅ **Design moderno** con layout responsive
- ✅ **Jekyll configurato** per GitHub Pages
- ✅ **Link funzionanti** con percorsi corretti
- ✅ **Documentazione completa** con wiki
- ✅ **SEO ottimizzato** con meta tag
- ✅ **Performance** con CSS ottimizzato

**URL finale**: https://gpicchiarelli.github.io/Colibri-DB/

Il sito presenta Colibrì DB come un prodotto enterprise-grade con design professionale e funzionalità complete! 🚀
