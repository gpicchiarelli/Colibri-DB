# 🚀 Deployment Guide - ColibrìDB Website

Guida completa per il deployment del sito web ColibrìDB su varie piattaforme.

## 📋 Pre-requisiti

- Repository Git configurato
- Accesso alle piattaforme di hosting
- File del sito nella cartella `website/`

## 🌐 Opzioni di Deployment

### 1. GitHub Pages (Consigliato)

#### Setup Automatico

Il repository include già un GitHub Actions workflow (`.github/workflows/deploy-website.yml`) che effettua il deploy automatico.

**Steps:**

1. **Abilita GitHub Pages nel repository:**
   - Vai su Settings → Pages
   - Source: GitHub Actions
   - Salva

2. **Push del codice:**
   ```bash
   git add website/
   git commit -m "Add website"
   git push origin main
   ```

3. **Verifica il deploy:**
   - Vai su Actions tab
   - Controlla il workflow "Deploy Website to GitHub Pages"
   - Il sito sarà disponibile su: `https://[username].github.io/Colibri-DB/`

#### Deploy Manuale

```bash
# Metodo 1: Subtree push
git subtree push --prefix website origin gh-pages

# Metodo 2: gh-pages npm package
npm install -g gh-pages
gh-pages -d website
```

---

### 2. Netlify

#### Deploy via UI

1. Vai su [netlify.com](https://netlify.com)
2. Click "Add new site" → "Import an existing project"
3. Connetti il repository GitHub
4. Configurazione:
   - Base directory: `website`
   - Build command: (lascia vuoto)
   - Publish directory: `website`
5. Click "Deploy site"

#### Deploy via CLI

```bash
# Installa Netlify CLI
npm install -g netlify-cli

# Login
netlify login

# Deploy
cd website
netlify deploy --prod
```

#### Deploy via Drag & Drop

1. Vai su [netlify.com/drop](https://netlify.com/drop)
2. Trascina la cartella `website/`
3. Sito deployato istantaneamente!

**File di configurazione:** `netlify.toml` già presente nella cartella `website/`

---

### 3. Vercel

#### Deploy via CLI

```bash
# Installa Vercel CLI
npm install -g vercel

# Login
vercel login

# Deploy
cd website
vercel --prod
```

#### Deploy via GitHub Integration

1. Vai su [vercel.com](https://vercel.com)
2. Click "Add New Project"
3. Import repository GitHub
4. Configurazione:
   - Root Directory: `website`
   - Framework Preset: Other
5. Deploy

**File di configurazione:** `vercel.json` già presente nella cartella `website/`

---

### 4. Cloudflare Pages

#### Deploy via Dashboard

1. Vai su [dash.cloudflare.com](https://dash.cloudflare.com)
2. Pages → "Create a project"
3. Connetti repository GitHub
4. Configurazione:
   - Build command: (lascia vuoto)
   - Build output directory: `website`
5. Save and Deploy

#### Deploy via Wrangler CLI

```bash
# Installa Wrangler
npm install -g wrangler

# Login
wrangler login

# Deploy
cd website
wrangler pages publish . --project-name=colibridb
```

---

### 5. AWS S3 + CloudFront

```bash
# Crea bucket S3
aws s3 mb s3://colibridb-website

# Carica file
aws s3 sync website/ s3://colibridb-website --acl public-read

# Configura come sito statico
aws s3 website s3://colibridb-website \
  --index-document index.html \
  --error-document 404.html

# (Opzionale) Configura CloudFront per CDN
```

---

### 6. Firebase Hosting

```bash
# Installa Firebase CLI
npm install -g firebase-tools

# Login
firebase login

# Init
firebase init hosting

# Deploy
firebase deploy --only hosting
```

Configurazione `firebase.json`:
```json
{
  "hosting": {
    "public": "website",
    "ignore": ["firebase.json", "**/.*", "**/node_modules/**"]
  }
}
```

---

### 7. Render

1. Vai su [render.com](https://render.com)
2. New → Static Site
3. Connetti repository
4. Configurazione:
   - Build Command: (lascia vuoto)
   - Publish Directory: `website`
5. Create Static Site

---

### 8. Azure Static Web Apps

```bash
# Installa Azure CLI
curl -sL https://aka.ms/InstallAzureCLIDeb | sudo bash

# Login
az login

# Deploy
az staticwebapp create \
  --name colibridb \
  --resource-group myResourceGroup \
  --source website/ \
  --location "West Europe"
```

---

### 9. DigitalOcean App Platform

1. Vai su [cloud.digitalocean.com](https://cloud.digitalocean.com)
2. Create → Apps
3. Connetti repository GitHub
4. Configurazione:
   - Type: Static Site
   - Source Directory: `website`
5. Deploy

---

### 10. Self-Hosted (Server Proprio)

#### Apache

```bash
# Copia file nel document root
sudo cp -r website/* /var/www/html/

# Riavvia Apache
sudo systemctl restart apache2
```

Il file `.htaccess` è già configurato nella cartella `website/`

#### Nginx

```nginx
# /etc/nginx/sites-available/colibridb
server {
    listen 80;
    server_name colibridb.com;
    root /var/www/colibridb;
    index index.html;

    location / {
        try_files $uri $uri/ =404;
    }

    # Gzip compression
    gzip on;
    gzip_types text/css application/javascript image/svg+xml;
    
    # Cache headers
    location ~* \.(css|js|jpg|jpeg|png|gif|svg|woff|woff2)$ {
        expires 1y;
        add_header Cache-Control "public, immutable";
    }
}
```

```bash
# Copia file
sudo cp -r website/* /var/www/colibridb/

# Attiva configurazione
sudo ln -s /etc/nginx/sites-available/colibridb /etc/nginx/sites-enabled/

# Riavvia Nginx
sudo systemctl restart nginx
```

---

## 🔒 HTTPS / SSL

### Cloudflare (Gratuito)

1. Aggiungi dominio a Cloudflare
2. SSL/TLS → Full
3. Always Use HTTPS: ON

### Let's Encrypt (Gratuito)

```bash
# Installa Certbot
sudo apt install certbot python3-certbot-nginx

# Ottieni certificato
sudo certbot --nginx -d colibridb.com -d www.colibridb.com

# Rinnovo automatico
sudo certbot renew --dry-run
```

---

## 📊 Post-Deployment

### 1. Verifica Funzionamento

```bash
# Test HTTP status
curl -I https://your-site.com

# Test performance
lighthouse https://your-site.com --view
```

### 2. Configura Analytics (Opzionale)

**Google Analytics:**
Aggiungi prima del tag `</head>` in `index.html`:

```html
<!-- Google Analytics -->
<script async src="https://www.googletagmanager.com/gtag/js?id=G-XXXXXXXXXX"></script>
<script>
  window.dataLayer = window.dataLayer || [];
  function gtag(){dataLayer.push(arguments);}
  gtag('js', new Date());
  gtag('config', 'G-XXXXXXXXXX');
</script>
```

**Plausible Analytics (Privacy-friendly):**

```html
<script defer data-domain="your-domain.com" src="https://plausible.io/js/script.js"></script>
```

### 3. Configura Custom Domain

#### GitHub Pages

1. Settings → Pages → Custom domain
2. Aggiungi il tuo dominio
3. Configura DNS:
   ```
   A     @     185.199.108.153
   A     @     185.199.109.153
   A     @     185.199.110.153
   A     @     185.199.111.153
   CNAME www   [username].github.io
   ```

#### Netlify/Vercel

1. Dashboard → Domain settings
2. Add custom domain
3. Segui le istruzioni DNS

---

## 🐛 Troubleshooting

### Issue: 404 su GitHub Pages

**Soluzione:**
```bash
# Verifica che il branch gh-pages esista
git branch -a

# Forza push
git subtree push --prefix website origin gh-pages --force
```

### Issue: File non aggiornati

**Soluzione:**
1. Svuota cache CDN
2. Hard refresh (Ctrl+Shift+R)
3. Verifica cache headers

### Issue: Stili non caricati

**Soluzione:**
1. Verifica path relativi in `index.html`
2. Controlla CORS headers
3. Verifica MIME types

---

## 📈 Ottimizzazioni

### Minification

```bash
# HTML
npm install -g html-minifier
html-minifier --collapse-whitespace --remove-comments index.html -o index.min.html

# CSS
npm install -g clean-css-cli
cleancss -o styles.min.css styles.css

# JavaScript
npm install -g terser
terser script.js -o script.min.js -c -m
```

### Image Optimization (se aggiungi immagini)

```bash
npm install -g imagemin-cli
imagemin images/* --out-dir=images/optimized
```

---

## ✅ Checklist Pre-Deploy

- [ ] Test locale funzionante
- [ ] Link interni funzionanti
- [ ] Link esterni funzionanti
- [ ] Responsive design testato
- [ ] Cross-browser testing (Chrome, Firefox, Safari)
- [ ] Performance Lighthouse > 90
- [ ] SEO meta tags configurati
- [ ] Favicon presente
- [ ] 404 page configurata
- [ ] robots.txt e sitemap.xml presenti
- [ ] HTTPS configurato
- [ ] Analytics configurato (opzionale)

---

## 📚 Risorse Utili

- [GitHub Pages Docs](https://docs.github.com/pages)
- [Netlify Docs](https://docs.netlify.com/)
- [Vercel Docs](https://vercel.com/docs)
- [Cloudflare Pages Docs](https://developers.cloudflare.com/pages/)
- [Google Lighthouse](https://developers.google.com/web/tools/lighthouse)

---

**Hai domande?** Apri un issue su GitHub o consulta la documentazione della piattaforma scelta.

**Made with ❤️ for ColibrìDB**

