# 🚀 Configurazione GitHub Pages per ColibrDB

## 📋 Setup GitHub Pages

### 1. Abilita GitHub Pages nel Repository

1. Vai su GitHub: `https://github.com/gpicchiarelli/Colibri-DB`
2. Clicca su **Settings** (scheda del repository)
3. Scorri verso il basso fino a **Pages** (sidebar sinistra)
4. In **Source**, seleziona **GitHub Actions**
5. Salva le impostazioni

### 2. Configurazione Automatica

Il repository è già configurato con:

✅ **Workflow GitHub Actions** (`.github/workflows/pages.yml`)
✅ **Configurazione Jekyll** (`_config.yml`)
✅ **Setup automatico GitHub Pages** (no Gemfile necessario)
✅ **Plugins supportati**: jekyll-feed, jekyll-seo-tag, jekyll-sitemap

### 3. Deployment Automatico

Una volta abilitato GitHub Pages, il sito si aggiornerà automaticamente:

- **Push su main branch** → Build e deploy automatico
- **Pull Request** → Build di test (non deploy)

### 4. URL del Sito

Il sito sarà disponibile su:
**https://gpicchiarelli.github.io/Colibri-DB/**

## 🔧 Configurazione Locale (Opzionale)

GitHub Pages gestisce tutto automaticamente! Non serve configurazione locale.

Per testare il contenuto:
1. Modifica i file markdown
2. Fai push su GitHub
3. Il sito si aggiorna automaticamente

## 📁 Struttura per GitHub Pages

```
ColibrDB/
├── .github/workflows/pages.yml    # ✅ Workflow automatico
├── _config.yml                    # ✅ Configurazione completa
├── .nojekyll                      # ✅ File speciale GitHub Pages
├── _layouts/                      # ✅ Layout personalizzati
├── wiki/                          # ✅ Documentazione wiki
├── docs/                          # ✅ Documentazione tecnica
├── index.md                       # ✅ Homepage
└── [altri file markdown]         # ✅ Tutti i contenuti
```

## 🎯 Funzionalità GitHub Pages

### ✅ **Supportate**
- Jekyll 4.x con GitHub Pages
- Plugins: feed, seo-tag, sitemap
- Layout personalizzati
- CSS personalizzato
- Markdown con frontmatter
- Link interni con `{{ site.baseurl }}`

### ✅ **URLs Corretti**
- Homepage: `/Colibri-DB/`
- Wiki: `/Colibri-DB/wiki/`
- Docs: `/Colibri-DB/docs/`
- API: `/Colibri-DB/feed.xml`, `/Colibri-DB/sitemap.xml`

## 🚨 Troubleshooting

### Problema: Build Fallisce
```bash
# Controlla i log in GitHub Actions
# Vai su: Actions → Deploy GitHub Pages
```

### Problema: Link Non Funzionano
- Verifica che tutti i link usino `{{ site.baseurl }}`
- Controlla che il baseurl sia `/Colibri-DB`

### Problema: CSS Non Si Carica
- Verifica che i file CSS siano in `docs/assets/css/`
- Controlla i percorsi nei layout

### Problema: Pagine Non Trovate
- Verifica che i file abbiano frontmatter corretto
- Controlla i permalink nelle configurazioni

## 📊 Monitoraggio

### GitHub Actions
- **Build Status**: https://github.com/gpicchiarelli/Colibri-DB/actions
- **Pages Deploy**: https://github.com/gpicchiarelli/Colibri-DB/deployments

### Analytics (Opzionale)
Puoi aggiungere Google Analytics modificando `_config.yml`:
```yaml
google_analytics: UA-XXXXXXXXX-X
```

## 🎉 Risultato Finale

Dopo il setup, avrai:
- ✅ Sito automaticamente aggiornato ad ogni push
- ✅ URL pulito: `https://gpicchiarelli.github.io/Colibri-DB/`
- ✅ SEO ottimizzato con sitemap automatico
- ✅ Feed RSS automatico
- ✅ Design responsive e moderno
- ✅ Navigazione completa wiki + docs

## 🔗 Link Utili

- **GitHub Pages Docs**: https://docs.github.com/en/pages
- **Jekyll Docs**: https://jekyllrb.com/docs/
- **Minima Theme**: https://github.com/jekyll/minima
- **Repository**: https://github.com/gpicchiarelli/Colibri-DB
