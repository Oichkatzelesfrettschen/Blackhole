#!/bin/sh
set -eu

usage() {
    printf '%s\n' \
        "usage: $0 --repo PATH --out PATH [--local-head COMMIT] [--merge-head COMMIT]" \
        "" \
        "Reconstruct the archived minix318 merge state from Git objects instead of" \
        "storing a giant diff or bundle in this repository." \
        "" \
        "If the local head commit is not present in PATH, restore it from a local" \
        "bundle first or fetch the ref that contains it. This script never writes" \
        "inside the source checkout; it creates a detached worktree under --out."
}

repo=
out=
local_head="a50957dcc3df264fac12adc67da36343a150658d"
merge_head="c9a4d1a581ea3d18f42860e7a4b102a3275ec6de"

while [ "$#" -gt 0 ]; do
    case "$1" in
        --repo)
            repo=$2
            shift 2
            ;;
        --out)
            out=$2
            shift 2
            ;;
        --local-head)
            local_head=$2
            shift 2
            ;;
        --merge-head)
            merge_head=$2
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            usage >&2
            exit 2
            ;;
    esac
done

if [ -z "$repo" ] || [ -z "$out" ]; then
    usage >&2
    exit 2
fi

if [ ! -d "$repo/.git" ]; then
    printf 'repo is not a Git checkout: %s\n' "$repo" >&2
    exit 2
fi

mkdir -p "$out"
worktree=$out/worktree
report=$out/report
rm -rf "$worktree" "$report"
mkdir -p "$report"

git -C "$repo" cat-file -e "$local_head^{commit}"
git -C "$repo" cat-file -e "$merge_head^{commit}"

git -C "$repo" worktree add --detach "$worktree" "$local_head"

set +e
git -C "$worktree" merge --no-commit "$merge_head" >"$report/merge.stdout" 2>"$report/merge.stderr"
merge_rc=$?
set -e
printf '%s\n' "$merge_rc" >"$report/merge-exit-code.txt"

git -C "$worktree" status --short >"$report/status-short.txt"
git -C "$worktree" status --porcelain=v1 >"$report/status-porcelain.txt"
git -C "$worktree" diff --cached --stat >"$report/diff-cached-stat.txt"
git -C "$worktree" diff --name-only --diff-filter=U >"$report/unmerged-paths.txt"

awk '{ counts[$1]++ } END { for (code in counts) print code, counts[code] }' \
    "$report/status-short.txt" | sort >"$report/status-code-counts.txt"

if [ "$merge_rc" -eq 0 ]; then
    printf '%s\n' "warning: merge completed cleanly; archived state expected conflicts" >&2
fi

printf '%s\n' "reconstructed merge state in $worktree"
printf '%s\n' "report written to $report"
