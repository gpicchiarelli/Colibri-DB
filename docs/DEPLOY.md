# Deploy su GitHub Pages

## 🚀 Configurazione GitHub Pages

### 1. Abilita GitHub Pages

1. Vai su GitHub → Settings del repository
2. Scorri fino a "Pages" nella sidebar
3. In "Source" seleziona "Deploy from a branch"
4. Scegli branch `main` e folder `/docs`
5. Clicca "Save"

### 2. URL del Sito

Il sito sarà disponibile su:
```
https://gpicchiarelli.github.io/Colibri-DB/
```

### 3. Configurazione Automatica

GitHub Pages utilizzerà automaticamente:
- Jekyll per il build
- La configurazione in `_config.yml`
- I file nella cartella `docs/`

## 🔧 Configurazione Locale (Opzionale)

### Test Locale

```bash
# Installa Ruby e Bundler
gem install bundler

# Installa le dipendenze
bundle install

# Avvia il server locale
bundle exec jekyll serve

# Il sito sarà su http://localhost:4000/Colibri-DB/
```

### Build Locale

```bash
# Build del sito
bundle exec jekyll build

# I file generati saranno in _site/
```

## 📁 Struttura per GitHub Pages

```
Colibri-DB/
├── docs/                 # Cartella sorgente
│   ├── _config.yml      # Configurazione Jekyll
│   ├── _layouts/        # Layout HTML
│   ├── _includes/       # Include HTML
│   ├── assets/          # CSS, JS, immagini
│   ├── wiki/            # Documentazione
│   ├── index.html       # Homepage
│   ├── architecture.html
│   ├── tla-specifications.html
│   └── Gemfile          # Dipendenze Ruby
└── README.md            # Documentazione progetto
```

## ⚙️ Configurazione Jekyll

### _config.yml

```yaml
title: "Colibrì DB"
description: "RDBMS professionale per macOS"
baseurl: "/Colibri-DB"  # Nome del repository
url: "https://gpicchiarelli.github.io"

# Build settings
markdown: kramdown
highlighter: rouge

# Collections
collections:
  wiki:
    output: true
    permalink: /wiki/:name/

# Defaults
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

# Plugins supportati da GitHub Pages
plugins:
  - jekyll-feed
  - jekyll-sitemap
  - jekyll-seo-tag
```

### Gemfile

```ruby
source "https://rubygems.org"
gem "github-pages", group: :jekyll_plugins
```

## 🔗 Link e Percorsi

### Link Interni

Tutti i link interni devono usare `relative_url`:

```html
<a href="{{ '/architecture.html' | relative_url }}">Architettura</a>
<a href="{{ '/wiki/Home.html' | relative_url }}">Wiki</a>
```

### Asset

Gli asset devono usare `relative_url`:

```html
<link rel="stylesheet" href="{{ '/assets/css/main.css' | relative_url }}">
```

## 🐛 Troubleshooting

### Problemi Comuni

1. **404 su GitHub Pages**
   - Verifica che `baseurl` sia corretto (`/Colibri-DB`)
   - Controlla che i file siano nella cartella `docs/`

2. **CSS non caricato**
   - Verifica i percorsi degli asset
   - Controlla che `assets/` sia nella root di `docs/`

3. **Jekyll non funziona**
   - GitHub Pages usa Jekyll automaticamente
   - Per test locale: `bundle exec jekyll serve`

4. **Link non funzionanti**
   - Usa sempre `| relative_url` per i link interni
   - Verifica che i file esistano

### Debug

```bash
# Build con debug
bundle exec jekyll build --verbose --trace

# Serve con debug
bundle exec jekyll serve --verbose --trace
```

## 📊 Monitoraggio

### GitHub Actions (Opzionale)

Puoi aggiungere GitHub Actions per build automatici:

```yaml
# .github/workflows/pages.yml
name: Deploy to GitHub Pages
on:
  push:
    branches: [ main ]
    paths: [ 'docs/**' ]
jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions/setup-ruby@v1
        with:
          ruby-version: '3.0'
      - run: |
          cd docs
          bundle install
          bundle exec jekyll build
      - uses: peaceiris/actions-gh-pages@v3
        with:
          github_token: ${{ secrets.GITHUB_TOKEN }}
          publish_dir: ./docs/_site
```

## ✅ Checklist Deploy

- [ ] Repository pubblico su GitHub
- [ ] Cartella `docs/` nella root del repository
- [ ] File `_config.yml` configurato correttamente
- [ ] `baseurl` impostato su `/Colibri-DB`
- [ ] GitHub Pages abilitato
- [ ] Branch `main` selezionato
- [ ] Folder `/docs` selezionato
- [ ] Sito accessibile su `https://gpicchiarelli.github.io/Colibri-DB/`

## 🎉 Risultato

Dopo il deploy, il sito sarà disponibile su:
**https://gpicchiarelli.github.io/Colibri-DB/**

Tutti i link funzioneranno correttamente e il sito avrà un design professionale e moderno!
