#!/usr/bin/env bash
# Blocks git commit/push/checkout/switch/branch-delete operations that would
# operate on (or move HEAD off) any branch other than $ALLOWED_BRANCH.
set -euo pipefail

ALLOWED_BRANCH="agent"
REPO_DIR="${CLAUDE_PROJECT_DIR:-.}"

input="$(cat)"
cmd="$(printf '%s' "$input" | jq -r '.tool_input.command // empty')"

[ -z "$cmd" ] && { echo '{}'; exit 0; }

# fast path: no "git" token anywhere in the command
case "$cmd" in
  *git*) ;;
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

# split on ; && || | so each chained sub-command is checked independently
# (best-effort; does not attempt full shell parsing/quoting)
normalized="$(printf '%s' "$cmd" | sed -E 's/&&|\|\||;|\|/\n/g')"

while IFS= read -r seg; do
  trimmed="$(printf '%s' "$seg" | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')"
  [ -z "$trimmed" ] && continue

  IFS=' ' read -ra words <<< "$trimmed"

  # find "git" as a bare word, skipping leading env-var assignments (FOO=bar git ...)
  gi=-1
  for i in "${!words[@]}"; do
    w="${words[$i]}"
    if [ "$w" = "git" ]; then gi=$i; break; fi
    case "$w" in
      *=*) continue ;;
      *) break ;;
    esac
  done
  [ "$gi" -lt 0 ] && continue

  sub="${words[$((gi+1))]:-}"

  # safely slice words[] starting at index $1 (avoids "unbound variable" on empty slices under set -u)
  rest=()
  start=$((gi+2))
  if [ "$start" -lt "${#words[@]}" ]; then
    rest=("${words[@]:$start}")
  fi

  case "$sub" in
    commit)
      if [ "$current_branch" != "$ALLOWED_BRANCH" ]; then
        deny "git commit is only allowed on the '$ALLOWED_BRANCH' branch (currently on '$current_branch')."
      fi
      ;;

    push)
      if [ "$current_branch" != "$ALLOWED_BRANCH" ]; then
        deny "git push is only allowed while on the '$ALLOWED_BRANCH' branch (currently on '$current_branch')."
      fi
      for arg in "${rest[@]+"${rest[@]}"}"; do
        case "$arg" in
          -*) continue ;;                       # flags
          *:*)
            dst="${arg#*:}"
            dst="${dst#refs/heads/}"
            if [ -n "$dst" ] && [ "$dst" != "$ALLOWED_BRANCH" ] && [ "$dst" != "HEAD" ]; then
              deny "git push targets ref '$dst'; only '$ALLOWED_BRANCH' is allowed."
            fi
            ;;
          origin|upstream|origin/*|upstream/*) continue ;;   # remote name, best-effort skip
          HEAD|"$ALLOWED_BRANCH") continue ;;
          *)
            deny "git push targets '$arg'; only '$ALLOWED_BRANCH' is allowed."
            ;;
        esac
      done
      ;;

    checkout|switch)
      target=""
      for arg in "${rest[@]+"${rest[@]}"}"; do
        case "$arg" in
          --) target="__PATHS__"; break ;;      # `git checkout -- <path>` file-restore form
          -b|-B|-c|-C) continue ;;               # create-branch flags; branch name caught below
          -*) continue ;;
          *) target="$arg"; break ;;
        esac
      done
      if [ "$target" = "__PATHS__" ]; then
        : # restoring files, not switching branches: allowed
      elif [ -n "$target" ] && [ "$target" != "$ALLOWED_BRANCH" ]; then
        deny "'$sub $target' would move off the '$ALLOWED_BRANCH' branch. Use 'git checkout -- <path>' to restore files without switching branches."
      fi
      ;;

    branch)
      for arg in "${rest[@]+"${rest[@]}"}"; do
        case "$arg" in
          -D|-d|-M|-m|--delete|--move)
            deny "'git branch $arg' modifies branches other than the checked-out '$ALLOWED_BRANCH' branch and is disabled."
            ;;
        esac
      done
      ;;
  esac
done <<< "$normalized"

echo '{}'
