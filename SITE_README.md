# 🐦 ColibrìDB Website

Questo è il sito web di ColibrìDB, costruito con Jekyll e GitHub Pages.

## 🚀 Test Locale

Per testare il sito localmente, segui questi passaggi:

### Prerequisiti
- Ruby 3.1+ (raccomandato)
- Bundler gem

### Installazione
```bash
# Installa le dipendenze
bundle install

# Avvia il server di sviluppo
bundle exec jekyll serve

# Il sito sarà disponibile su http://localhost:4000
```

### Build per Produzione
```bash
# Genera il sito statico
bundle exec jekyll build

# I file generati saranno nella cartella _site/
```

## 📁 Struttura del Sito

```
├── _config.yml          # Configurazione Jekyll
├── _layouts/            # Layout HTML
│   └── default.html     # Layout principale
├── index.md             # Pagina principale
├── wiki/                # Pagine della wiki
│   ├── Quick-Start.md
│   ├── Architecture.md
│   ├── CLI-Reference.md
│   ├── API-Reference.md
│   ├── Configuration.md
│   ├── Development.md
│   ├── Performance.md
│   ├── Troubleshooting.md
│   ├── Examples.md
│   └── Home.md
└── docs/                # Documentazione tecnica
    └── ...
```

## 🎨 Design

Il sito utilizza un design moderno e responsive con:
- **Header** con gradient blu e badge informativi
- **Navigazione** sticky con link alle sezioni principali
- **Cards** per le caratteristiche e sezioni
- **Sintassi highlighting** per i blocchi di codice
- **Design responsive** per mobile e desktop

## 🔧 Personalizzazione

### Modificare il Layout
Edita `_layouts/default.html` per modificare l'aspetto generale del sito.

### Aggiungere Pagine Wiki
1. Crea un nuovo file `.md` nella cartella `wiki/`
2. Aggiungi il front matter Jekyll:
   ```yaml
   ---
   layout: page
   title: Nome Pagina
   description: Descrizione della pagina
   ---
   ```
3. Aggiungi il link alla navigazione in `_layouts/default.html`

### Modificare la Configurazione
Edita `_config.yml` per modificare:
- Titolo e descrizione del sito
- URL e baseurl
- Collezioni (wiki, docs)
- Plugin Jekyll

## 🚀 Deploy

Il sito è configurato per il deploy automatico su GitHub Pages tramite GitHub Actions. Ogni push sul branch `main` attiva automaticamente il build e il deploy.

### Workflow GitHub Actions
Il file `.github/workflows/pages.yml` contiene la configurazione per:
1. Checkout del codice
2. Setup di Ruby e Bundler
3. Build di Jekyll
4. Deploy su GitHub Pages

## 📚 Documentazione

- **Wiki Operativa**: Guide pratiche per l'uso di ColibrìDB
- **Manuale Tecnico**: Documentazione approfondita per sviluppatori
- **API Reference**: Documentazione completa delle API
- **Esempi**: Casi d'uso pratici e tutorial

## 🐛 Troubleshooting

### Errori di Build
1. Verifica che tutti i file markdown abbiano il front matter corretto
2. Controlla la sintassi YAML in `_config.yml`
3. Assicurati che i link interni siano corretti

### Problemi di Stile
1. Verifica che il CSS sia incluso nel layout
2. Controlla che le classi CSS siano corrette
3. Testa la responsività su diversi dispositivi

## 📞 Supporto

Per problemi con il sito web:
- Apri una [issue su GitHub](https://github.com/gpicchiarelli/Colibri-DB/issues)
- Consulta la [documentazione Jekyll](https://jekyllrb.com/docs/)
- Verifica la [documentazione GitHub Pages](https://docs.github.com/en/pages)
