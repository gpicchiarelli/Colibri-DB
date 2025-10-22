# ColibrìDB Documentation

This is the documentation site for ColibrìDB, a high-performance relational database management system for macOS written in Swift 6.2.

## 🚀 Quick Start

Il sito è configurato per funzionare con GitHub Pages e Jekyll.

### Sviluppo Locale

```bash
# Installa le dipendenze
bundle install

# Avvia il server di sviluppo
bundle exec jekyll serve

# Il sito sarà disponibile su http://localhost:4000
```

### Build per Produzione

```bash
# Build del sito
bundle exec jekyll build

# I file generati saranno nella cartella _site/
```

## 📁 Struttura del Sito

```
docs/
├── _config.yml          # Configurazione Jekyll
├── _layouts/            # Layout HTML
│   ├── default.html     # Layout principale
│   └── doc.html         # Layout per documentazione
├── _includes/           # Include HTML riutilizzabili
├── assets/              # CSS, JS, immagini
│   └── css/
│       └── main.css     # Stili principali
├── wiki/                # Documentazione wiki
├── index.html           # Homepage
├── architecture.html    # Pagina architettura
├── tla-specifications.html # Specifiche TLA+
└── Gemfile             # Dipendenze Ruby
```

## 🎨 Design System

Il sito utilizza un design system moderno con:

- **Colori**: Palette professionale con primary, secondary, accent
- **Tipografia**: Inter per testi, JetBrains Mono per codice
- **Layout**: Grid system responsive
- **Componenti**: Card, bottoni, sezioni modulari
- **Animazioni**: Transizioni fluide e micro-interazioni

## 🔧 Configurazione

### GitHub Pages

Il sito è configurato per funzionare automaticamente con GitHub Pages:

1. Push del codice su GitHub
2. Abilita GitHub Pages nelle impostazioni del repository
3. Seleziona "Deploy from a branch" e scegli `main` / `docs`
4. Il sito sarà disponibile su `https://gpicchiarelli.github.io/Colibri-DB`

### Variabili d'Ambiente

- `baseurl`: `/Colibri-DB` (nome del repository)
- `url`: `https://gpicchiarelli.github.io`

## 📝 Contenuti

### Aggiungere Nuove Pagine

1. Crea un file `.html` o `.md` nella root di `docs/`
2. Aggiungi il front matter YAML:

```yaml
---
layout: default
title: "Titolo Pagina"
description: "Descrizione per SEO"
---
```

### Aggiungere Documentazione Wiki

1. Crea un file `.md` nella cartella `wiki/`
2. Il layout `doc` sarà applicato automaticamente
3. I link funzioneranno come `/wiki/nome-pagina/`

## 🚀 Deploy

### Automatico (GitHub Pages)

Il deploy è automatico quando pushi su GitHub.

### Manuale

```bash
# Build
bundle exec jekyll build

# Upload della cartella _site/ al tuo server
```

## 🐛 Troubleshooting

### Errori Comuni

1. **CSS non caricato**: Verifica che `baseurl` sia corretto
2. **Link non funzionanti**: Controlla i percorsi relativi
3. **Jekyll non funziona**: Esegui `bundle install`

### Debug

```bash
# Build con debug
bundle exec jekyll build --verbose

# Serve con debug
bundle exec jekyll serve --verbose --trace
```

## 📚 Risorse

- [Jekyll Documentation](https://jekyllrb.com/docs/)
- [GitHub Pages](https://pages.github.com/)
- [Liquid Template Language](https://shopify.github.io/liquid/)

---

**Colibrì DB** - RDBMS professionale per macOS con verifiche formali complete.