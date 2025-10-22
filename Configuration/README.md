# Configuration

This directory contains shared configuration files for development tools used in the ColibrìDB project.

## Files

### `swiftformat.yml`
SwiftFormat configuration file that defines code formatting rules aligned with the project's style guidelines.

**Usage:**
```bash
swiftformat . --config Configuration/swiftformat.yml
```

### `swiftlint.yml`
SwiftLint configuration file focused on safety checks and stylistic guidance for Swift code.

**Usage:**
```bash
swiftlint --config Configuration/swiftlint.yml
```

## Integration

These configuration files are automatically used by:
- **Local Development**: When running `make format` and `make lint`
- **CI/CD**: GitHub Actions workflows use these configurations
- **IDE**: Most Swift IDEs can be configured to use these files

## Customization

To modify formatting or linting rules:
1. Edit the appropriate configuration file
2. Test changes locally with `make quality`
3. Update documentation if needed
4. Submit changes via pull request

## Best Practices

- Keep configurations consistent across the project
- Document any non-standard rules
- Test configuration changes before committing
- Consider impact on existing codebase when changing rules
