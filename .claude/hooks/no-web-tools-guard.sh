#!/usr/bin/env bash
# Unconditionally blocks WebFetch/WebSearch, which reach arbitrary internet
# hosts rather than Claude's own servers.
set -euo pipefail

input="$(cat)"
tool="$(printf '%s' "$input" | jq -r '.tool_name // "this tool"')"

jq -n --arg reason "$tool reaches the internet and is disabled by the no-internet restriction for this project (only Claude's own servers may be reached)." '{
  hookSpecificOutput: {
    hookEventName: "PreToolUse",
    permissionDecision: "deny",
    permissionDecisionReason: $reason
  }
}'
