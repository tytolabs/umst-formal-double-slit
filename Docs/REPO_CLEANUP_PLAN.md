# Repository cleanup, doc check & polish — plan

Use this as a **checklist** for a human or agent pass. Tackle phases in order; **P0** unblocks correctness and links.

---

## P0 — Broken links, canonical names, truth in docs *(do first)*

| # | Task | How to verify |
|---|------|----------------|
| P0.1 | **Doc index:** ensure `Docs/DEEP_VERIFICATION_REPORT.md` exists at this **exact** path (case-sensitive for Linux CI). Remove any duplicate `deep_verification_report.md` if it reappears. | `ls Docs/DEEP_VERIFICATION_REPORT.md` |
| P0.2 | **Linked files exist:** `README.md` + `PARALLEL_WORK.md` reference `VENDOR_SYNC`, `SCOPE_PARENT_AND_SEPARATE_REPO`, verification docs — confirm all resolve. | `ls Docs/VENDOR_SYNC.md` etc. |
| P0.3 | **`Docs/TODO-TRACKING.md` § `a1-measurement-cost`:** update “Coq/Agda not in repository” — **false** once `Coq/` and `Agda/` exist; say **partial** (only Landauer bridge + Agda stub). | Read § cross-lang |
| P0.4 | **`CHANGELOG.md` historical bullets:** scan for stale claims (e.g. old **CLAIMED** rows that are now **DONE**). Either add “(historical)” or trim in a dedicated “changelog hygiene” commit. | Manual read |
| P0.5 | **`Coq/` build artifacts:** ensure `*.glob`, `*.vo`, `.*.aux` are **not** committed (`.gitignore` already lists them). If tracked, `git rm --cached`. | `git status Coq/` |

---

## P1 — Generated / local artifacts *(repo hygiene)*

| # | Task | Notes |
|---|------|--------|
| P1.1 | **`sim/out/`** | Decide: **gitignore** default outputs (`*.csv`, `*.svg`, `*.png`, `*.gif`) *or* keep a **small** committed fixture set. Document the rule in `sim/README.md`. |
| P1.2 | **`Haskell/dist-newstyle/`** | Already gitignored; ensure no stray copies under version control. |
| P1.3 | **`Lean/.lake/`** | Never commit; confirm `.gitignore` / CI caches only. |

---

## P2 — Documentation polish *(consistency pass)*

| Area | Files to read end-to-end | Goal |
|------|---------------------------|------|
| **Root** | `README.md`, `CONTRIBUTING.md`, `CHANGELOG.md` | Align “vendored / upstream” wording; ensure CI commands match `Makefile`; no duplicate narratives. |
| **Docs/** | `PARALLEL_WORK.md`, `TODO-TRACKING.md`, `ASSUMPTIONS-DOUBLE-SLIT.md`, `DoubleSlit-Derivation.md`, `EpistemicSensingQuantum.md`, `Mathematical-Foundations.md` | One glossary for “upstream vs vendored”; cross-links; table rows match disk (`glob`). |
| **Lean** | `Lean/VERIFY.md`, `Lean/lakefile.lean` | Root count = table coverage; note sorries + `physicalSecondLaw` axiom. |
| **Haskell** | `Haskell/README.md`, `Haskell/CHANGELOG.md`, `*.cabal` | Fill empty `synopsis:` / set `license:` if you publish; `exposed-modules` = `src/*.hs`. |
| **sim** | `sim/README.md`, `requirements-optional.txt` | Script inventory vs `sim/*.py`; skip behavior documented. |
| **CI** | `.github/workflows/lean.yml`, `haskell.yml` | Match `make ci-local` / `ci-full`; document path-filter tradeoff in `PARALLEL_WORK`. |
| **Formal extras** | `Coq/README.md`, `Agda/` | Agda: add `README.md` one-pager if module count grows. |

**Optional:** add **`Docs/README.md`** — bullet index of all `Docs/*.md` + one-line purpose.

---

## P3 — Code polish *(non-functional)*

| Track | Action |
|-------|--------|
| **Lean** | Comment headers on the 10 `sorry` sites pointing to a single tracking issue or `PROOF-STATUS.md` row; grep project `Lean` only for `sorry` (exclude `.lake`). |
| **Haskell** | `-Wall` cleanup where easy; unify `landauerBitEnergy` story (long-term: one canonical re-export). |
| **Python** | `ruff` / `black` optional; docstrings on public `main()` scripts; shebang consistency. |

---

## P4 — “Check each file” workflow *(mechanical)*

For a full audit pass:

1. **Inventory:** `find` / `glob` by directory: `Lean/*.lean`, `Haskell/src/*.hs`, `Haskell/test/*.hs`, `sim/*.py`, `sim/tests/*.py`, `Docs/*.md`, `.github/workflows/*.yml`, `scripts/*`, `Coq/*`, `Agda/*`.
2. **Per file:** exists in README or VERIFY or sim README? Any dead internal link (`grep '\](Docs/'`)?
3. **Build:** `make ci-full` + optional `make coq-check` `make agda-check`.
4. **Record:** append a row to **`Docs/DEEP_VERIFICATION_REPORT.md`** §0 with date + commit SHA, or start **`Docs/AUDIT_LOG.md`** for dated passes.

---

## Suggested sequencing (one PR or sprint)

1. **PR-A (P0):** link fixes, `TODO-TRACKING` Coq/Agda wording, remove duplicate verification filename, untrack Coq artifacts if any.  
2. **PR-B (P1 + P2):** `sim/out` policy + doc index + README/CHANGELOG trim.  
3. **PR-C (P3):** style / comments / optional formatters.

---

## Quick commands

```bash
# Broken markdown links (if markdown-link-check installed)
# npx markdown-link-check README.md Docs/*.md

# Project sorries only
rg '^\s*sorry\b' Lean --glob '*.lean' --glob '!**/.lake/**'

# Lake roots vs .lean files in Lean/ (manual diff)
rg -o '`[A-Z][a-zA-Z0-9]*`' Lean/lakefile.lean
ls Lean/*.lean | xargs -n1 basename
```

---

*Related:* `Docs/AGENT_VERIFICATION_PROMPT.md` (re-verify after cleanup) · `Docs/VENDOR_SYNC.md` (upstream sync)
