#!/usr/bin/env bash
# Blocks Bash commands that reach the internet.
# Exception: git fetch/pull/push/ls-remote against this repo's already-configured
# remote are allowed (git push is additionally restricted to the 'agent' branch
# by git-branch-guard.sh). git clone and git remote add/set-url are still blocked,
# since they can point the repo at a new, untrusted network location.
set -euo pipefail

input="$(cat)"
cmd="$(printf '%s' "$input" | jq -r '.tool_input.command // empty')"
[ -z "$cmd" ] && { echo '{}'; exit 0; }

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

ALWAYS_NETWORK=" curl wget http https httpie nc ncat netcat telnet ftp sftp ssh scp rsync aria2c axel docker "
PKG_MANAGERS=" pip pip3 pipx poetry npm npx yarn pnpm gem cargo go brew apt apt-get yum dnf apk conda "
NETWORK_SUBCMDS=" install download wheel update upgrade add publish get tap push pull sync "

normalized="$(printf '%s' "$cmd" | sed -E 's/&&|\|\||;|\|/\n/g')"

while IFS= read -r seg; do
  trimmed="$(printf '%s' "$seg" | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')"
  [ -z "$trimmed" ] && continue

  IFS=' ' read -ra words <<< "$trimmed"
  [ "${#words[@]}" -eq 0 ] && continue

  # find first real word, skipping leading env-var assignments and sudo
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
  base="${base##*/}"   # strip a path prefix like /usr/bin/curl

  # treat "python -m pip ..." / "python3 -m pip ..." like "pip ..."
  if [ "$base" = "python" ] || [ "$base" = "python3" ]; then
    nxt="${words[$((ci+1))]:-}"
    if [ "$nxt" = "-m" ]; then
      base="${words[$((ci+2))]:-}"
      ci=$((ci+2))
    fi
  fi

  case "$ALWAYS_NETWORK" in
    *" $base "*)
      deny "'$base' reaches the internet and is disabled by the no-internet restriction for this project."
      ;;
  esac

  case "$PKG_MANAGERS" in
    *" $base "*)
      sub="${words[$((ci+1))]:-}"
      case "$NETWORK_SUBCMDS" in
        *" $sub "*)
          deny "'$base $sub' reaches the internet and is disabled by the no-internet restriction for this project."
          ;;
      esac
      ;;
  esac

  if [ "$base" = "git" ]; then
    sub="${words[$((ci+1))]:-}"
    case "$sub" in
      clone)
        deny "'git clone' reaches the internet and is disabled by the no-internet restriction for this project."
        ;;
      remote)
        rest=()
        start=$((ci+2))
        if [ "$start" -lt "${#words[@]}" ]; then rest=("${words[@]:$start}"); fi
        for arg in "${rest[@]+"${rest[@]}"}"; do
          case "$arg" in
            add|set-url)
              deny "'git remote $arg' can redirect where this repo pushes/fetches and is disabled by the no-internet restriction."
              ;;
          esac
        done
        ;;
      # fetch/pull/push/ls-remote against the existing configured remote are allowed
    esac
  fi

done <<< "$normalized"

echo '{}'
