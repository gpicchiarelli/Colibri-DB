# Prototypes

This directory keeps experimental or legacy code that is not part of the active
SwiftPM build. The goal is to preserve it for reference without polluting
`Sources/`.

- `ColibriServerHTTP/` — early Foundation-based HTTP server prototype that still
  refers to the non-existent `ColibriDB` façade.
- `Examples/` — walkthrough scripts that need porting to the stabilised APIs
  before being published again.

The developer tooling previously shipped as `coldb-dev` has been promoted into
the `ColibriDevTools` SwiftPM target.
