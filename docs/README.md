# Colibrì DB Documentation Site

Sito web moderno per la documentazione di Colibrì DB, un RDBMS sperimentale ad alte prestazioni per macOS.

## 🚀 Caratteristiche

- **Design Moderno**: Interfaccia ispirata ad Apple e GitHub con design system coerente
- **Responsive**: Ottimizzato per desktop, tablet e mobile
- **Performance**: Caricamento veloce con CSS ottimizzato e font system
- **SEO**: Meta tag completi e struttura semantica
- **Accessibilità**: Controlli di accessibilità e navigazione keyboard-friendly

## 📁 Struttura

```
docs/
├── _config.yml              # Configurazione Jekyll
├── _layouts/
│   └── default.html         # Layout principale
├── index.html               # Homepage
├── architecture.html        # Pagina architettura
├── tla-specifications.html  # Pagina specifiche TLA+
├── wiki/                    # Documentazione wiki
└── README.md               # Questo file
```

## 🎨 Design System

### Colori
- **Primary**: #000000 (Nero)
- **Secondary**: #007AFF (Blu Apple)
- **Accent**: #FF6B35 (Arancione)
- **Success**: #34C759 (Verde)
- **Warning**: #FF9500 (Arancione)
- **Error**: #FF3B30 (Rosso)

### Tipografia
- **Font System**: -apple-system, BlinkMacSystemFont, 'SF Pro Display'
- **Font Mono**: 'SF Mono', Monaco, 'Cascadia Code'

### Spacing
- **xs**: 0.25rem
- **sm**: 0.5rem
- **md**: 1rem
- **lg**: 1.5rem
- **xl**: 2rem
- **2xl**: 3rem
- **3xl**: 4rem
- **4xl**: 6rem

## 📱 Pagine

### Homepage (`index.html`)
- Hero section con call-to-action
- Caratteristiche principali del database
- Architettura modulare
- Moduli implementati
- Quick start con esempi di codice
- Performance target
- Call-to-action finale

### Architettura (`architecture.html`)
- Panoramica architettura a livelli
- Diagramma modulare interattivo
- Specifiche TLA+ complete
- Dettagli moduli con esempi di codice
- Tab interattivi per ogni modulo

### TLA+ Specifications (`tla-specifications.html`)
- Statistiche verifiche formali
- Grid moduli TLA+ con status
- Esempi di codice TLA+
- Risultati verifica TLC
- Invarianti e proprietà di liveness

## 🛠️ Sviluppo

### Prerequisiti
- Ruby 2.7+
- Jekyll 4.0+
- Bundler

### Installazione
```bash
# Clona il repository
git clone https://github.com/gpicchiarelli/Colibri-DB.git
cd Colibri-DB/docs

# Installa dipendenze
bundle install

# Avvia server locale
bundle exec jekyll serve

# Apri http://localhost:4000
```

### Build Produzione
```bash
# Build per produzione
bundle exec jekyll build

# Output in _site/
```

## 📝 Contenuti

### Moduli Documentati
1. **Schema Evolution** - Gestione evoluzione schema
2. **Statistics Maintenance** - Aggiornamento statistiche
3. **Connection Pooling** - Gestione pool connessioni
4. **Memory Management** - Gestione memoria avanzata
5. **Compression** - Compressione dati
6. **Monitoring** - Sistema di monitoraggio
7. **Backup & Restore** - Sistema backup completo
8. **Point-in-Time Recovery** - Recovery temporale

### Specifiche TLA+
- 149 specifiche TLA+ complete
- Invarianti di sicurezza verificate
- Proprietà di liveness garantite
- Model checking automatico con TLC

## 🎯 Obiettivi

### Performance
- Caricamento < 2 secondi
- Lighthouse Score > 90
- Core Web Vitals ottimali

### SEO
- Meta tag completi
- Struttura semantica
- Sitemap automatica
- Open Graph tags

### Accessibilità
- WCAG 2.1 AA compliance
- Navigazione keyboard
- Screen reader friendly
- Contrasto colori ottimale

## 🔧 Personalizzazione

### Aggiungere Pagine
1. Crea file HTML in root
2. Usa layout `default`
3. Aggiungi navigazione in `_config.yml`

### Modificare Stili
1. Modifica CSS inline nelle pagine
2. Per stili globali, aggiorna `_layouts/default.html`
3. Usa variabili CSS per consistenza

### Aggiungere Moduli
1. Aggiungi card in `modules-grid`
2. Crea sezione dettagli in `module-details`
3. Aggiungi tab in `module-tabs`

## 📊 Analytics

Il sito è configurato per:
- Google Analytics (se configurato)
- Jekyll SEO Tag
- Sitemap automatica
- Feed RSS

## 🚀 Deploy

### GitHub Pages
```bash
# Push su branch gh-pages
git subtree push --prefix docs origin gh-pages
```

### Netlify
```bash
# Build command
bundle exec jekyll build

# Publish directory
_site
```

### Vercel
```bash
# Build command
bundle exec jekyll build

# Output directory
_site
```

## 📄 Licenza

Questo sito è parte del progetto Colibrì DB e segue la stessa licenza del progetto principale.

## 🤝 Contribuire

1. Fork del repository
2. Crea branch per feature
3. Modifica documentazione
4. Testa localmente
5. Crea pull request

## 📞 Supporto

- **Issues**: [GitHub Issues](https://github.com/gpicchiarelli/Colibri-DB/issues)
- **Discussions**: [GitHub Discussions](https://github.com/gpicchiarelli/Colibri-DB/discussions)
- **Email**: support@colibridb.dev

---

**Autore**: Colibrì DB Team  
**Data**: 2025-10-22  
**Versione**: 1.0.0