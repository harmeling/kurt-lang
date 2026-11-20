#!/usr/bin/env python3
"""Which commit has the `kurt.py` with this fingerprint? `kurt -v` shows the first 12 hex digits of the
SHA-256 of the bytes of `kurt.py` (`file_fingerprint` in kurt.py); this script looks for them in the history
of a git repository (kurt-lang-dev with all its commits, or kurt-lang with one commit per release).

Usage:
    python3 scripts/find_commit.py SHA [--repo DIR ...] [--standalone REV ...]

    SHA          the fingerprint, or any prefix of it (at least 6 digits)
    --repo DIR   a repository to search (default: the repository of this script; repeat it for several, e.g.
                 `--repo ../kurt-lang-dev --repo ../kurt-lang`)
    --standalone REV
                 also compare the single-file bundle (`scripts/build_standalone.py`, it embeds the theories, so
                 its fingerprint is not that of any file in git) built at REV (a tag or a commit; repeat it,
                 e.g. `--standalone v0.13.1`). A bundle is built from a checkout of REV, which takes a minute.

A pip install and a git checkout run the same `kurt.py` as the repository has, so the plain search finds them.
Of several commits with the same `kurt.py` (a commit that does not touch it has its parent's), the oldest is
printed first; a file with local changes that were never committed matches nothing.
"""
import argparse
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def git(repo: Path, *args: str, text: bool = True):
    done = subprocess.run(['git', '-C', str(repo), *args], capture_output=True, text=text, check=True)
    return done.stdout


def fingerprint(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()[:12]


def search(repo: Path, wanted: str) -> list[str]:
    """The commits of the repository (oldest first) whose `kurt.py` has the fingerprint `wanted` (a prefix)."""
    # every (commit, blob) in which a file called kurt.py changed; a blob is hashed once
    log = git(repo, 'log', '--all', '--reverse', '--format=commit %H', '--raw', '--no-abbrev', '--', ':(glob)**/kurt.py')
    commits_of_blob: dict[str, list[str]] = {}
    commit = ''
    for line in log.splitlines():
        if line.startswith('commit '):
            commit = line[len('commit '):]
        elif line.startswith(':'):
            fields = line.split('\t')[0].split()
            blob = fields[3]
            if set(blob) != {'0'}:                    # a deleted file has the null blob
                commits_of_blob.setdefault(blob, []).append(commit)
    found: list[str] = []
    for blob, commits in commits_of_blob.items():
        if fingerprint(git(repo, 'cat-file', 'blob', blob, text=False)).startswith(wanted):
            found.extend(commits)
    return found


def describe(repo: Path, commit: str) -> str:
    line = git(repo, 'log', '-1', '--format=%h %ad %s', '--date=short', commit).strip()
    tags = git(repo, 'tag', '--points-at', commit).split()
    return line + (f'   [{", ".join(tags)}]' if tags else '')


def standalone_fingerprint(repo: Path, rev: str) -> str:
    """The fingerprint of the bundle built from a checkout of `rev`."""
    with tempfile.TemporaryDirectory() as tmp:
        tree = Path(tmp) / 'tree'
        tree.mkdir()
        archive = subprocess.run(['git', '-C', str(repo), 'archive', rev], capture_output=True, check=True).stdout
        subprocess.run(['tar', '-x', '-C', str(tree)], input=archive, check=True)
        out = Path(tmp) / 'kurt.py'
        subprocess.run([sys.executable, str(tree / 'scripts' / 'build_standalone.py'), '-o', str(out)],
                       cwd=tree, check=True, capture_output=True)
        return fingerprint(out.read_bytes())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('sha', help='the fingerprint shown by `kurt -v`, or a prefix of it')
    parser.add_argument('--repo', type=Path, action='append', help='a repository to search (default: this one)')
    parser.add_argument('--standalone', action='append', default=[], metavar='REV',
                        help='also build the single-file bundle at REV and compare')
    args = parser.parse_args()
    wanted = args.sha.strip().lower()
    if len(wanted) < 6 or any(c not in '0123456789abcdef' for c in wanted):
        parser.error('SHA must be at least 6 hexadecimal digits')
    repos = [r.resolve() for r in (args.repo or [REPO_ROOT])]
    hit = False
    for repo in repos:
        commits = search(repo, wanted)
        print(f'{repo.name}: ' + ('no commit has this kurt.py' if not commits else f'{len(commits)} commit(s), oldest first'))
        for c in commits:
            print('   ', describe(repo, c))
        hit = hit or bool(commits)
        for rev in args.standalone:
            try:
                digest = standalone_fingerprint(repo, rev)
            except subprocess.CalledProcessError as error:
                print(f'    standalone bundle at {rev}: not built ({(error.stderr or b"").decode(errors="replace").strip()[-200:]})')
                continue
            same = digest.startswith(wanted)
            print(f'    standalone bundle at {rev}: {digest}' + ('   <-- the same' if same else ''))
            hit = hit or same
    if not hit:
        print('Not found: a version with local changes, a commit of another repository, or a bundle (try --standalone REV).')
    return 0 if hit else 1


if __name__ == '__main__':
    sys.exit(main())
