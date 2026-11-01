# Releasing

The checklist for 0.1.0, the first release. Every step that publishes something (the tag, the GitHub release, the
Bend hub package) is the maintainer's call; nothing here runs automatically.

## Before the tag

1. `main` is green in GitHub Actions on both runners (`.github/workflows/ci.yml`: `make ci` on macos-15 and
   ubuntu-24.04), and `make ci` passes locally on the pinned toolchain (`TOOLCHAIN`).
2. Timing claims: either a quiet-machine run (1-minute load < 2 before each run; `make m2-bench LABEL=v010`, then
   `make tpch`) replaces the PROVISIONAL numbers in `README.md` "Performance", or they stay labelled PROVISIONAL.
3. `CHANGELOG.md`: the heading `## 0.1.0 (unreleased)` becomes `## 0.1.0 (<date>)`; `README.md`'s first status
   paragraph ("Not released yet") says 0.1.0 is released.
4. `plans/STATUS.md` records the final `make ci` run (commit, date, duration).

## The release

5. Tag and push: `git tag -a v0.1.0 -m "bend-frame 0.1.0"` then `git push origin v0.1.0`.
6. GitHub release from the tag, its notes being `CHANGELOG.md`'s 0.1.0 section:
   `gh release create v0.1.0 --title "bend-frame 0.1.0" --notes-file <that section>`.
7. Bend hub (optional, separate decision): `bend login`, then `bend frame.bend --publish bend-frame@0.1.0.0`
   (`bend --publish` has no dry-run mode, so `make consumer-check` is the closest rehearsal: a clean clone builds
   and runs the quickstart and a relative and an absolute import consumer). Afterwards `README.md`'s Quickstart shows
   the import by package name.

## After

8. A new `## Unreleased` heading at the top of `CHANGELOG.md`.
