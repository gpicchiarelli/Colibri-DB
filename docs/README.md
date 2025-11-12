# 🐦 ColibrìDB Website

Sito web ultra-minimalista in stile Apple per ColibrìDB - Database Relazionale con verifica formale TLA+.

## 🎨 Design

- **Stile**: Minimalismo Apple con animazioni fluide
- **Tecnologie**: HTML5, CSS3, JavaScript vanilla
- **Features**: 
  - Glassmorphism effects
  - Smooth scroll animations
  - Intersection Observer API
  - Counter animations
  - Parallax scrolling
  - Gradient animations
  - Tilt effects su hover
  - Copy-to-clipboard
  - Responsive design completo

## 🚀 Quick Start

### Sviluppo Locale

1. **Apri il file HTML**:
   ```bash
   open index.html
   ```
   
   Oppure usa un server locale:
   ```bash
   # Python 3
   python3 -m http.server 8000
   
   # Node.js (http-server)
   npx http-server -p 8000
   
   # PHP
   php -S localhost:8000
   ```

2. **Visita**: http://localhost:8000

### Deployment

#### GitHub Pages
```bash
# 1. Push nella branch gh-pages
git subtree push --prefix website origin gh-pages

# 2. Abilita GitHub Pages nelle impostazioni del repo
```

#### Netlify
1. Drag & drop della cartella `website` su netlify.com
2. Oppure connetti il repo GitHub

#### Vercel
```bash
vercel --prod
```

## 📁 Struttura

```
website/
├── index.html          # Pagina principale
├── styles.css          # Tutti gli stili (CSS moderno)
├── script.js           # JavaScript per animazioni
└── README.md           # Questo file
```

## ✨ Features Principali

### 1. Hero Section
- Animazioni fade-in
- Counter animati per le statistiche
- Gradient text animato
- Scroll indicator animato

### 2. Features Grid
- Card con hover effects
- Tilt effect 3D al passaggio del mouse
- Tags con stili personalizzati
- Icone emoji animate

### 3. Architecture Diagram
- Layers interattivi
- Hover effects con bordo colorato
- Animazione sequenziale al caricamento

### 4. Quick Start
- Step numerati con design minimalista
- Code block con syntax highlighting
- Copy-to-clipboard funzionante
- Design responsive

### 5. Performance Metrics
- Card con metriche in tempo reale
- Progress bar animate
- Hover effects

### 6. Academic Papers
- Timeline dei paper implementati
- Design pulito e leggibile

### 7. CTA & Footer
- Gradient background animato
- Pattern sottile in movimento
- Footer completo con link

## 🎯 Ottimizzazioni

### Performance
- ✅ Zero dipendenze esterne (eccetto Google Fonts)
- ✅ CSS ottimizzato con variabili
- ✅ JavaScript vanilla (no framework)
- ✅ Lazy loading ready
- ✅ Smooth 60 FPS animations

### SEO
- ✅ HTML5 semantico
- ✅ Meta tags
- ✅ Open Graph ready
- ✅ Schema.org ready

### Accessibilità
- ✅ Contrasti WCAG AA compliant
- ✅ Focus states
- ✅ Responsive design
- ✅ Semantic HTML

## 🎨 Customizzazione

### Colori

Modifica le variabili CSS in `styles.css`:

```css
:root {
    --color-primary: #0071e3;      /* Blu principale */
    --color-gradient-1: #0071e3;   /* Gradient start */
    --color-gradient-2: #00c4cc;   /* Gradient end */
    --color-text: #1d1d1f;         /* Testo principale */
}
```

### Animazioni

Regola le animazioni in `script.js`:

```javascript
// Durata counter animation
const duration = 2000; // millisecondi

// Threshold per Intersection Observer
const observerOptions = {
    threshold: 0.1,
    rootMargin: '0px 0px -100px 0px'
};
```

## 🐛 Easter Eggs

Il sito include alcuni easter eggs:

1. **Konami Code**: ↑ ↑ ↓ ↓ ← → ← → B A
   - Attiva un effetto rainbow temporaneo

2. **Console Message**: 
   - Apri la console per vedere il logo ASCII

## 📱 Responsive Breakpoints

- **Desktop**: > 768px
- **Tablet**: 768px - 480px  
- **Mobile**: < 480px

## 🚀 Performance

- **Lighthouse Score**: 95+ (expected)
- **First Contentful Paint**: < 1s
- **Time to Interactive**: < 2s
- **Total Bundle Size**: < 50KB (minified)

## 🔧 Browser Support

- Chrome/Edge 90+
- Firefox 88+
- Safari 14+
- Opera 76+

## 📝 TODO

- [ ] Aggiungere dark mode
- [ ] Aggiungere più pagine (docs, api-reference, ecc.)
- [ ] Aggiungere search functionality
- [ ] Integrare con sistema di analytics
- [ ] Aggiungere immagini/screenshots
- [ ] Creare versione multilingua (EN/IT)
- [ ] Aggiungere blog section
- [ ] Integrare con GitHub API per stats real-time

## 🤝 Contributing

Per modificare il sito:

1. Modifica i file nella cartella `website/`
2. Testa localmente
3. Commit e push
4. Deploy automatico (se configurato)

## 📄 License

BSD-3-Clause - vedi LICENSE nel repository principale

---

**Made with ❤️ for ColibrìDB**

