# minix318 reproducible merge-state recipe

This directory replaces two oversized local artifacts with a reproducible
recipe:

- `diff-cached.patch`: 944 MB, derivable from the conflicted index.
- `minix318-local-history-before-origin-sync.bundle`: 383 MB, only needed if the
  local head commit is no longer present in any reachable clone.

The durable facts are small:

- local head: `a50957dcc3df264fac12adc67da36343a150658d`
- merge head: `c9a4d1a581ea3d18f42860e7a4b102a3275ec6de`
- final remote state after cleanup: `ec32c2ad3adef1dfd84ed0c9a822b76065d7138a`
- conflict inventory: `unmerged-paths.txt`
- status class counts: `status-code-counts.txt`
- source branch snapshot: `source-branches.txt`

Run the reconstruction against a clone that still has the local head object:

```sh
./reconstruct-merge-state.sh \
  --repo /home/eirikr/Github/OS-Projects/minix318 \
  --out /tmp/minix318-merge-reconstruct
```

The script creates a detached worktree, replays the historical merge with
`git merge --no-commit`, and regenerates status, conflict, and cached-diff
statistics. It does not modify the source checkout.

The archived raw status also had one branch-status line and one untracked nested
checkout entry. Those were cleanup artifacts, not merge products, so
`status-code-counts.txt` records the reproducible merge classes only.

Exact byte-for-byte recovery of the deleted local-only head requires either a
clone that still contains `a50957dcc3df264fac12adc67da36343a150658d` or a small
future branch/ref that points to that commit. Storing the full bundle in this
repository was intentionally rejected because it would push Blackhole into large
object storage churn.
