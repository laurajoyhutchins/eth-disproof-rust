# Pre-publication branch snapshot

This commit is an **archive**, not implementation work. The tagged commit contains the source tree from `main` at `74277e22ded83a88432c94b048f81d8064b67446`, plus a machine-readable list of all 179 branch names and their exact commit IDs.

The synthetic intermediate merge commits make the recorded branch heads reachable from this tag. They do not merge old code into `main`. Do not merge or rebase this archive into active development.

To inspect the inventory:

```sh
git fetch origin tag pre-public-branch-snapshot-20261110
git show pre-public-branch-snapshot-20261110:PUBLICATION-ARCHIVE.json
```

To restore a branch, read its SHA from the manifest, then run `git branch restored/<name> <commit-sha>`. The repository remains private during cleanup. This tag is **not** a separate private backup, and its history will be publicly accessible if the repository is later made public.
