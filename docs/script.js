// ==========================================
// Smooth Scrolling & Navigation
// ==========================================
document.addEventListener('DOMContentLoaded', () => {
    initNavigation();
    initScrollAnimations();
    initCounters();
    initCopyButtons();
    initParallax();
});

// Navigation scroll effect
function initNavigation() {
    const nav = document.querySelector('.nav');
    
    window.addEventListener('scroll', () => {
        if (window.scrollY > 50) {
            nav.classList.add('scrolled');
        } else {
            nav.classList.remove('scrolled');
        }
    });
    
    // Smooth scroll for anchor links
    document.querySelectorAll('a[href^="#"]').forEach(anchor => {
        anchor.addEventListener('click', function (e) {
            e.preventDefault();
            const target = document.querySelector(this.getAttribute('href'));
            if (target) {
                const offset = 80; // Nav height
                const targetPosition = target.offsetTop - offset;
                window.scrollTo({
                    top: targetPosition,
                    behavior: 'smooth'
                });
            }
        });
    });
}

// ==========================================
// Intersection Observer for Animations
// ==========================================
function initScrollAnimations() {
    const observerOptions = {
        threshold: 0.1,
        rootMargin: '0px 0px -100px 0px'
    };
    
    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.classList.add('visible');
                
                // Trigger specific animations
                if (entry.target.classList.contains('stat-value')) {
                    animateCounter(entry.target);
                }
                
                if (entry.target.classList.contains('perf-bar')) {
                    animateBar(entry.target);
                }
            }
        });
    }, observerOptions);
    
    // Observe elements
    const animatedElements = document.querySelectorAll(`
        .feature-card,
        .arch-layer,
        .quickstart-step,
        .perf-card,
        .paper-card,
        .doc-link,
        .stat
    `);
    
    animatedElements.forEach(el => {
        el.classList.add('fade-in');
        observer.observe(el);
    });
}

// ==========================================
// Counter Animation
// ==========================================
function initCounters() {
    const counters = document.querySelectorAll('.stat-value');
    
    counters.forEach(counter => {
        counter.innerText = '0';
    });
}

function animateCounter(element) {
    const target = parseInt(element.getAttribute('data-count'));
    const duration = 2000; // 2 seconds
    const increment = target / (duration / 16); // 60 FPS
    let current = 0;
    
    const updateCounter = () => {
        current += increment;
        if (current < target) {
            element.innerText = formatNumber(Math.ceil(current));
            requestAnimationFrame(updateCounter);
        } else {
            element.innerText = formatNumber(target);
        }
    };
    
    updateCounter();
}

function formatNumber(num) {
    if (num >= 1000) {
        return (num / 1000).toFixed(0) + 'k+';
    }
    return num.toString();
}

// ==========================================
// Performance Bar Animation
// ==========================================
function animateBar(element) {
    setTimeout(() => {
        element.style.setProperty('--width', element.style.getPropertyValue('--width') || '0%');
    }, 300);
}

// ==========================================
// Copy to Clipboard
// ==========================================
function initCopyButtons() {
    const copyButtons = document.querySelectorAll('.copy-btn');
    
    copyButtons.forEach(button => {
        button.addEventListener('click', () => {
            const codeBlock = button.closest('.quickstart-code').querySelector('code');
            const text = codeBlock.textContent;
            
            navigator.clipboard.writeText(text).then(() => {
                const originalText = button.textContent;
                button.textContent = 'Copied!';
                button.style.background = 'rgba(0, 255, 0, 0.3)';
                
                setTimeout(() => {
                    button.textContent = originalText;
                    button.style.background = '';
                }, 2000);
            }).catch(err => {
                console.error('Failed to copy:', err);
            });
        });
    });
}

// ==========================================
// Parallax Effect
// ==========================================
function initParallax() {
    let ticking = false;
    
    window.addEventListener('scroll', () => {
        if (!ticking) {
            window.requestAnimationFrame(() => {
                updateParallax();
                ticking = false;
            });
            ticking = true;
        }
    });
}

function updateParallax() {
    const scrolled = window.pageYOffset;
    const hero = document.querySelector('.hero');
    
    if (hero) {
        const heroContent = hero.querySelector('.hero-content');
        if (heroContent) {
            heroContent.style.transform = `translateY(${scrolled * 0.3}px)`;
            heroContent.style.opacity = 1 - (scrolled / 600);
        }
    }
}

// ==========================================
// Feature Cards Tilt Effect
// ==========================================
document.querySelectorAll('.feature-card').forEach(card => {
    card.addEventListener('mousemove', (e) => {
        const rect = card.getBoundingClientRect();
        const x = e.clientX - rect.left;
        const y = e.clientY - rect.top;
        
        const centerX = rect.width / 2;
        const centerY = rect.height / 2;
        
        const rotateX = (y - centerY) / 20;
        const rotateY = (centerX - x) / 20;
        
        card.style.transform = `perspective(1000px) rotateX(${rotateX}deg) rotateY(${rotateY}deg) translateY(-8px)`;
    });
    
    card.addEventListener('mouseleave', () => {
        card.style.transform = '';
    });
});

// ==========================================
// Architecture Layers Sequential Animation
// ==========================================
const archLayers = document.querySelectorAll('.arch-layer');
archLayers.forEach((layer, index) => {
    layer.style.animationDelay = `${index * 0.1}s`;
});

// ==========================================
// Gradient Animation on Scroll
// ==========================================
window.addEventListener('scroll', () => {
    const gradientTexts = document.querySelectorAll('.gradient-text');
    const scrollProgress = window.pageYOffset / (document.documentElement.scrollHeight - window.innerHeight);
    
    gradientTexts.forEach(text => {
        const hue = scrollProgress * 60; // Shift hue based on scroll
        text.style.filter = `hue-rotate(${hue}deg)`;
    });
});

// ==========================================
// Performance Metrics Real-time Update
// ==========================================
function simulateMetrics() {
    const metrics = [
        { element: '.perf-metric', values: ['50,000+', '51,234', '49,876', '52,100'] },
    ];
    
    // This is just for demo purposes
    // In production, you'd fetch real metrics from your API
}

// ==========================================
// Lazy Loading for Images (if added)
// ==========================================
if ('IntersectionObserver' in window) {
    const imageObserver = new IntersectionObserver((entries, observer) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                const img = entry.target;
                img.src = img.dataset.src;
                img.classList.add('loaded');
                observer.unobserve(img);
            }
        });
    });
    
    document.querySelectorAll('img[data-src]').forEach(img => {
        imageObserver.observe(img);
    });
}

// ==========================================
// Easter Egg: Konami Code
// ==========================================
let konamiCode = ['ArrowUp', 'ArrowUp', 'ArrowDown', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'ArrowLeft', 'ArrowRight', 'b', 'a'];
let konamiIndex = 0;

document.addEventListener('keydown', (e) => {
    if (e.key === konamiCode[konamiIndex]) {
        konamiIndex++;
        if (konamiIndex === konamiCode.length) {
            activateEasterEgg();
            konamiIndex = 0;
        }
    } else {
        konamiIndex = 0;
    }
});

function activateEasterEgg() {
    document.body.style.animation = 'rainbow 2s linear infinite';
    
    const style = document.createElement('style');
    style.textContent = `
        @keyframes rainbow {
            0% { filter: hue-rotate(0deg); }
            100% { filter: hue-rotate(360deg); }
        }
    `;
    document.head.appendChild(style);
    
    setTimeout(() => {
        document.body.style.animation = '';
    }, 5000);
    
    console.log('🎉 Easter egg activated! ColibrìDB is even more colorful now!');
}

// ==========================================
// Performance Monitoring
// ==========================================
if ('PerformanceObserver' in window) {
    // Monitor Core Web Vitals
    const observer = new PerformanceObserver((list) => {
        for (const entry of list.getEntries()) {
            console.log(`${entry.name}: ${entry.value}ms`);
        }
    });
    
    observer.observe({ entryTypes: ['measure', 'navigation', 'paint'] });
}

// ==========================================
// Dark Mode Toggle (Optional - commented out)
// ==========================================
/*
function initDarkMode() {
    const toggleButton = document.createElement('button');
    toggleButton.textContent = '🌙';
    toggleButton.className = 'dark-mode-toggle';
    toggleButton.style.cssText = `
        position: fixed;
        bottom: 2rem;
        right: 2rem;
        width: 50px;
        height: 50px;
        border-radius: 50%;
        border: none;
        background: var(--color-primary);
        color: white;
        font-size: 1.5rem;
        cursor: pointer;
        box-shadow: var(--shadow-lg);
        z-index: 1000;
        transition: transform 0.2s ease;
    `;
    
    toggleButton.addEventListener('click', () => {
        document.body.classList.toggle('dark-mode');
        toggleButton.textContent = document.body.classList.contains('dark-mode') ? '☀️' : '🌙';
    });
    
    toggleButton.addEventListener('mouseenter', () => {
        toggleButton.style.transform = 'scale(1.1) rotate(15deg)';
    });
    
    toggleButton.addEventListener('mouseleave', () => {
        toggleButton.style.transform = 'scale(1) rotate(0deg)';
    });
    
    document.body.appendChild(toggleButton);
}

// Uncomment to enable dark mode
// initDarkMode();
*/

// ==========================================
// Console Welcome Message
// ==========================================
console.log(`
%c ColibrìDB 
%c RDBMS Production-Ready con TLA+ 

🚀 50,000+ TPS
🔬 69 Specifiche TLA+
⚡ <10ms p95 latency
🛡️ ACID completo

GitHub: https://github.com/gpicchiarelli/Colibri-DB
`,
'font-size: 24px; font-weight: bold; color: #0071e3;',
'font-size: 14px; color: #6e6e73;'
);

