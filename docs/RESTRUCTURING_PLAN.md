# ColibrDB Restructuring Blueprint

## Key Findings
- **Sources/** mixes active targets with prototypes (e.g. `ColibriServer`, `coldb-dev`) that never build, confusing maintainers and tooling.
- **ColibriCore** holds unrelated subsystems flat (Buffer, Catalog, WAL, Planner, Monitoring...), which blocks modular builds and targeted tests.
- **Server implementations** are duplicated: `Sources/ColibriServer` (Foundation-based) and `Sources/coldb-server` (SwiftNIO). The former references non-existent symbols (`ColibriDB`) and cannot compile.
- **Docs & assets** include shadow copies with suffix ` 2` (e.g. `docs/index 2.html`, `.nojekyll 2`, `docs/wiki/... 2.md`), likely merge artefacts now polluting the tree.
- **Data fixtures** exist in both `data/` and `data 2/`, and build artefacts leak into version control (`.build/... 2.*`).
- **Configuration** for developer tooling (formatting, linting) is scattered or missing; there is no canonical style configuration.

## Multi-Phase Reorganization Plan

### Phase 0 — Baseline Cleanup (today → short-term)
1. Remove or relocate stray duplicates with suffix ` 2` (docs, data, config) into a dedicated `Archive/` if still valuable.
2. Move non-target prototypes (`Sources/ColibriServer`, `Sources/coldb-dev`) out of `Sources/` into `Prototypes/` to make `swift build` reflect the true deliverables.
3. Ensure `data/` hosts reusable fixtures and exclude/clean `.build/` detritus; add gitignores where needed.
4. Establish a `Configuration/` area for shared configs (`colibridb.conf.json`, lint settings) instead of keeping them in the root.

### Phase 1 — Target Realignment
1. Split `ColibriCore` into focused SwiftPM targets (e.g. `ColibriFoundation`, `ColibriStorage`, `ColibriTransactions`, `ColibriSQL`) to trim compile times and allow selective testing.
2. Promote the SwiftNIO server to a `ColibriServer` target (renaming current `coldb-server`) and treat the HTTP prototype as an example or integration test.
3. Convert the user CLI into a dedicated `ColibriCLI` target, keeping `coldb` as the executable wrapper; relocate shared CLI helpers to a library target.
4. Introduce a dedicated `ColibriDevTools` target collecting the advanced dev CLI, reporting, and monitoring utilities currently under `coldb-dev`.

### Phase 2 — Documentation & Operations
1. Consolidate `docs/`, `_layouts/`, `wiki/`, and `Examples/` under a `Documentation/` umbrella with clear `website/`, `guides/`, `examples/` subfolders.
2. Remove stale manual HTML copies in favor of the Jekyll-powered site; version design drafts in `Documentation/drafts/`.
3. Add a `docs/architecture/` section describing the new target layout, dependency graph, and module responsibilities.
4. Automate doc linting (link checker, spell checker) via CI to prevent diverging duplicates.

### Phase 3 — Tooling & Quality Gates
1. Introduce SwiftFormat/SwiftLint configs in `Configuration/`, hook them up in CI, and add `make format`/`make lint` helpers.
2. Expand the existing test suite to respect the modular split (per-target test bundles); add integration smoke tests for server + CLI flows.
3. Define reproducible benchmark harness scripts, stored under `Tools/Benchmarks/`, separating them from shipping executables.
4. Document the maintenance process (release checklist, tagging) reflecting the reorganized repository.

## Immediate Next Steps
- Execute Phase 0 step 1–2 in this iteration (clean duplicates, relocate prototypes).
- Draft gitignore updates for build artefacts and experimental data sets.
- Prepare follow-up issues/PRs for the multi-target split to avoid an oversized change set.

## Follow-Up Issue Candidates
- Track the `ColibriCore` modular split (Storage, Transactions, SQL, Telemetry) so each layer can build and test in isolation.
- Promote the SwiftNIO server (`ColibriServer`) with integration tests and remove the defunct Foundation prototype once parity is achieved.
- Rebuild the Examples/ scripts against the new library targets and reintroduce them as verified documentation samples.
- Add CI jobs for `swiftformat`/`swiftlint` using the new configuration files and document a pre-commit workflow.
