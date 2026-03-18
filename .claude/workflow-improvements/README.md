# Workflow Improvements

Custom Lean tactics and workflow tools to build. All motivated by pain points in actual proofs.

| File | Tool | Effort | Description |
|------|------|--------|-------------|
| [chain-simp.md](chain-simp.md) | `@[chain_simp]` | Small | Curated simp extension for chain homotopy proofs |
| [normalize-proofs.md](normalize-proofs.md) | `normalize_proofs` | Small | Auto-unify duplicate proof witnesses via `Subsingleton.elim` |
| [name-parts.md](name-parts.md) | `name_parts` | Medium | Pattern-match goal structure and bind names without re-elaboration |
| [expr-diff.md](expr-diff.md) | `#diff` / `diff_goals` | Medium | Structural diff between expressions, exposing hidden differences |
| [linter-code-actions.md](linter-code-actions.md) | VS Code actions | Small | Auto-fix unused simp args, line length, etc. |
| [namespace-simp-filtering.md](namespace-simp-filtering.md) | `hsimp?` | Medium–Large | Namespace-level simp filtering (long-term ideal for abstraction control) |
