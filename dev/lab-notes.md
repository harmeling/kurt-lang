# Lab Notes — kurt-lang

Running log of agent-session setup and activity for this repo, on the
`agent` branch, per the `start-agent` skill.

## 2026-09-24

- Repo already existed on GitHub (`harmeling/kurt-lang`) with substantial
  prior history on `agent` (60+ commits: lambda-calculus implementation,
  matching-engine perf work, soundness fixes, tutorials) — cloned into
  `~/git/kurt-lang`, this is the first time it goes through the formal
  `start-agent` workflow. That prior history predates this log and isn't
  otherwise recorded here.
- `CLAUDE.md` already present (substantial, ~9KB) — skipped `/init`.
- No `lab-notes.md` existed — created this file.

## 2026-09-24 21:25 — kurt-lang-1 launch (idle, Remote Control), tmux-on-ls8-slurm scheme

- Launched idle — no task given, standing by for Remote Control.
- Session name: `kurt-lang-1`
- Claude Code session ID (transcript UUID, for `--resume`):
  `96063648-7312-499c-b272-dbfafd829507`
- Hit the first-run "trust this folder" prompt (new clone location on this
  host); confirmed with explicit user permission.
- Launch command used (run locally, already on `ls8-slurm`):
  `tmux new-session -d -s kurt-lang-1 -c ~/git/kurt-lang 'claude --remote-control kurt-lang-1'`
- Monitor: `tmux capture-pane -t kurt-lang-1 -p | tail -n 50`
- Attach: `tmux attach -t kurt-lang-1`
- Resume (after a kill or restart): use the `resume-agent` skill.
- Cancel: `tmux kill-session -t kurt-lang-1`
