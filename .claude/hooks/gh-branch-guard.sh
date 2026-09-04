#!/usr/bin/env bash
# Restricts `gh` (GitHub CLI) to PR operations scoped to the 'agent' branch,
# mirroring the git-push exception in git-branch-guard.sh. Everything else
# (issues, releases, repo/workflow/api/auth/etc., PRs for other branches) is
# disabled under the no-internet restriction.
set -euo pipefail

ALLOWED_BRANCH="agent"
REPO_DIR="${CLAUDE_PROJECT_DIR:-.}"

input="$(cat)"
cmd="$(printf '%s' "$input" | jq -r '.tool_input.command // empty')"
[ -z "$cmd" ] && { echo '{}'; exit 0; }

case "$cmd" in
  *gh*) ;;
  *) echo '{}'; exit 0 ;;
esac

deny() {
  jq -n --arg reason "$1" '{
    hookSpecificOutput: {
      hookEventName: "PreToolUse",
      permissionDecision: "deny",
      permissionDecisionReason: $reason
    }
  }'
  exit 0
}

current_branch="$(git -C "$REPO_DIR" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "")"

normalized="$(printf '%s' "$cmd" | sed -E 's/&&|\|\||;|\|/\n/g')"

while IFS= read -r seg; do
  trimmed="$(printf '%s' "$seg" | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')"
  [ -z "$trimmed" ] && continue

  IFS=' ' read -ra words <<< "$trimmed"
  [ "${#words[@]}" -eq 0 ] && continue

  ci=-1
  for i in "${!words[@]}"; do
    w="${words[$i]}"
    case "$w" in
      sudo) continue ;;
      *=*) continue ;;
      *) ci=$i; break ;;
    esac
  done
  [ "$ci" -lt 0 ] && continue

  base="${words[$ci]}"
  base="${base##*/}"
  [ "$base" != "gh" ] && continue

  top="${words[$((ci+1))]:-}"

  case "$top" in
    ""|--version|-v|help|--help|-h)
      continue
      ;;
    pr)
      : # validated below
      ;;
    *)
      deny "'gh $top' is disabled; only 'gh pr' operations for the '$ALLOWED_BRANCH' branch are allowed by the no-internet restriction."
      ;;
  esac

  prsub="${words[$((ci+2))]:-}"

  case "$prsub" in
    "")
      deny "'gh pr' requires a subcommand; bare 'gh pr' is disabled by the no-internet restriction."
      ;;

    checkout)
      deny "'gh pr checkout' would check out another branch and is disabled by the branch restriction."
      ;;

    create)
      head_val=""
      j=$((ci+3))
      while [ "$j" -lt "${#words[@]}" ]; do
        w="${words[$j]}"
        case "$w" in
          --head|-H) head_val="${words[$((j+1))]:-}"; j=$((j+2)) ;;
          --head=*)  head_val="${w#--head=}"; j=$((j+1)) ;;
          *)         j=$((j+1)) ;;
        esac
      done
      if [ -n "$head_val" ]; then
        if [ "$head_val" != "$ALLOWED_BRANCH" ]; then
          deny "'gh pr create --head $head_val' targets a branch other than '$ALLOWED_BRANCH' and is disabled."
        fi
      elif [ "$current_branch" != "$ALLOWED_BRANCH" ]; then
        deny "'gh pr create' is only allowed while on the '$ALLOWED_BRANCH' branch (currently on '$current_branch')."
      fi
      ;;

    list)
      has_head_filter=""
      j=$((ci+3))
      while [ "$j" -lt "${#words[@]}" ]; do
        w="${words[$j]}"
        case "$w" in
          --head|-H) v="${words[$((j+1))]:-}"; [ "$v" = "$ALLOWED_BRANCH" ] && has_head_filter=1; j=$((j+2)) ;;
          --head=*)  v="${w#--head=}"; [ "$v" = "$ALLOWED_BRANCH" ] && has_head_filter=1; j=$((j+1)) ;;
          *)         j=$((j+1)) ;;
        esac
      done
      if [ -z "$has_head_filter" ]; then
        deny "'gh pr list' must be filtered with --head $ALLOWED_BRANCH; unscoped PR listing is disabled by the no-internet restriction."
      fi
      ;;

    view|diff|checks|status|comment|edit|ready|review|close|reopen|merge)
      first_arg="${words[$((ci+3))]:-}"
      case "$first_arg" in
        ""|-*)
          # no explicit target, or first token is a flag: falls back to the current branch's PR
          if [ "$current_branch" != "$ALLOWED_BRANCH" ]; then
            deny "'gh pr $prsub' is only allowed while on the '$ALLOWED_BRANCH' branch (currently on '$current_branch')."
          fi
          ;;
        "$ALLOWED_BRANCH")
          : # explicit and matches
          ;;
        *)
          deny "'gh pr $prsub $first_arg' targets something other than the '$ALLOWED_BRANCH' branch and is disabled."
          ;;
      esac
      ;;

    *)
      deny "'gh pr $prsub' is not in the allowed set for the '$ALLOWED_BRANCH' branch and is disabled."
      ;;
  esac

done <<< "$normalized"

echo '{}'
