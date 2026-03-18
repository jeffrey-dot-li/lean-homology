#!/usr/bin/env bash
set -e

# Project root = parent of scripts/
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONFIG="$PROJECT_ROOT/mcp.toml"

if [[ ! -f "$CONFIG" ]]; then
  echo "mcp.toml not found at $CONFIG" >&2
  exit 1
fi

# Extract repo and commit from [lean-lsp] section (simple grep/sed, no extra deps)
REPO=$(sed -n '/^\[lean-lsp\]/,/^\[/p' "$CONFIG" | grep 'repo =' | head -1 | sed 's/.*"\([^"]*\)".*/\1/')
COMMIT=$(sed -n '/^\[lean-lsp\]/,/^\[/p' "$CONFIG" | grep 'commit =' | head -1 | sed 's/.*"\([^"]*\)".*/\1/')

if [[ -z "$REPO" || -z "$COMMIT" ]]; then
  echo "mcp.toml [lean-lsp] must contain repo = \"...\" and commit = \"...\"" >&2
  exit 1
fi

export PATH="$PROJECT_ROOT/.devenv/profile/bin:$PATH"
exec uvx --from "git+${REPO}@${COMMIT}" lean-lsp-mcp
