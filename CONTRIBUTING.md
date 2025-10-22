# Contributing to ColibrìDB

Thank you for your interest in contributing to ColibrìDB! We welcome issues, proposals, and pull requests.

## Development Environment

### Prerequisites
- macOS 13+
- Swift 6.2+
- Xcode 15+ (recommended)

### Local Build and Test

```bash
# Build the project
swift build

# Run tests
swift test

# Run benchmarks
swift run benchmarks
```

## Code Style

- **Swift 6**: Use modern Swift features, protocol-first design, typed errors
- **Focused Changes**: Keep changes focused and small
- **Documentation**: Update documentation (`docs/`) when modifying behaviors or APIs
- **Code Quality**: Run `swiftformat` and `swiftlint` with profiles in `Configuration/` before opening a PR

```bash
# Format code
swiftformat .

# Lint code
swiftlint
```

## Commit and PR Guidelines

### Commit Messages
- Use clear, descriptive titles
- Prefer [Conventional Commits](https://www.conventionalcommits.org/) format:
  - `feat:` for new features
  - `fix:` for bug fixes
  - `docs:` for documentation changes
  - `style:` for formatting changes
  - `refactor:` for code refactoring
  - `test:` for test additions/changes
  - `chore:` for maintenance tasks

### Pull Requests
- Associate PRs with issues when possible
- Provide comprehensive descriptions
- Include tests for new functionality
- Ensure all tests pass before submitting

## Development Workflow

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Make your changes
4. Run tests and linting
5. Commit your changes with conventional commit format
6. Push to your fork (`git push origin feature/amazing-feature`)
7. Open a Pull Request

## License

By contributing, you agree that your contributions will be licensed under the BSD 3-Clause License.

## Questions?

Feel free to open an issue for questions or discussions about the project.

