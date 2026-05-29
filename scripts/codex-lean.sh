#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LEAN_MCP_LAUNCHER="$PROJECT_ROOT/scripts/start-lean-mcp.sh"

exec codex \
  -C "$PROJECT_ROOT" \
  -c 'mcp_servers.lean-lsp.command="bash"' \
  -c "mcp_servers.lean-lsp.args=[\"-lc\",\"exec \\\"$LEAN_MCP_LAUNCHER\\\"\"]" \
  "$@"
