# ColibrìDB Documentation

This directory contains the complete documentation for ColibrìDB, a high-performance, multi-database management system designed for modern applications.

## Structure

```
docs/
├── README.md                    # This file
├── index.md                     # Main documentation index
├── _config.yml                  # Jekyll configuration
├── 01-introduction.md           # Introduction to ColibrìDB
├── 02-architecture.md           # System architecture
├── 03-installation.md           # Installation and setup
├── 04-core-concepts.md          # Core concepts and principles
├── 05-database-management.md    # Database management guide
├── 06-sql-reference.md          # SQL language reference
├── 07-cli-reference.md          # CLI command reference
├── 08-development-tools.md      # Development and debugging tools
├── 09-performance-tuning.md     # Performance optimization guide
├── 10-troubleshooting.md        # Troubleshooting guide
├── 11-api-reference.md          # API reference documentation
└── 12-contributing.md           # Contributing guide
```

## Building the Documentation

### Prerequisites
- Ruby 2.7 or later
- Jekyll 4.0 or later
- Bundler

### Setup
```bash
# Install dependencies
bundle install

# Serve locally
bundle exec jekyll serve

# Build for production
bundle exec jekyll build
```

### Viewing
- Local development: http://localhost:4000
- Production: https://colibridb.dev/docs

## Writing Guidelines

### Markdown Style
- Use standard Markdown syntax
- Include code examples with syntax highlighting
- Use descriptive headings and subheadings
- Include table of contents for long documents

### Code Examples
- Use Swift for code examples
- Include SQL examples where relevant
- Show CLI commands with proper formatting
- Include expected output where helpful

### Images and Diagrams
- Store images in `docs/images/`
- Use Mermaid for diagrams when possible
- Include alt text for accessibility
- Optimize images for web display

## Contributing

### Adding New Documentation
1. Create new markdown file in appropriate location
2. Follow naming convention: `##-topic.md`
3. Update `index.md` to include new document
4. Add to navigation in `_config.yml`
5. Submit pull request

### Updating Existing Documentation
1. Edit the relevant markdown file
2. Test locally with Jekyll
3. Update table of contents if needed
4. Submit pull request

### Review Process
- All documentation changes require review
- Ensure code examples are tested
- Check for broken links
- Verify formatting and style

## Style Guide

### Headings
- Use descriptive headings
- Follow hierarchy (H1 → H2 → H3)
- Include anchor links for long documents

### Code Blocks
- Use appropriate language identifiers
- Include line numbers for long examples
- Add comments to explain complex code

### Lists
- Use numbered lists for procedures
- Use bullet points for features
- Keep lists concise and scannable

### Tables
- Use tables for structured data
- Include headers for all columns
- Keep tables readable on mobile

## Maintenance

### Regular Tasks
- Check for broken links
- Update code examples
- Review and update outdated information
- Ensure consistency across documents

### Version Updates
- Update version numbers in examples
- Review API changes
- Update installation instructions
- Check compatibility information

## Feedback

### Issues
- Report documentation issues on GitHub
- Include specific page and section
- Describe the problem clearly
- Suggest improvements if possible

### Suggestions
- Suggest new documentation topics
- Propose improvements to existing content
- Share examples and use cases
- Help improve clarity and organization

## License

Documentation is licensed under the same BSD 3-Clause License as the main project.

---

*For questions about the documentation, please open an issue or contact the maintainers.*