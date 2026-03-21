# Scope: this repo vs “parent”, and going standalone

This note replaces confusing **fork** jargon with **what lives in this folder** vs **what lives somewhere else**.

## 1. Plain vocabulary

| Phrase in docs | Meaning |
|----------------|---------|
| **This repo / this checkout** | Everything under `umst-formal-double-slit/` (Lean, Haskell, sim, workflows). **If it’s not on disk here, it’s not “done” for this project.** |
| **Parent / base / `umst-formal`** | A **different** project (often the wider UMST formal repo). Some coordination docs said “DONE” for files that exist **there**, not **here**. That’s a documentation scope mix-up, not a hidden feature in your tree. |
| **Fork (GitHub)** | Historically this tree may have been **branched or copied** from another repo. **Operationally** you can ignore that: treat this directory as **one product** with its own `git` remote. |
| **Separate repo** | You `git init` (or create a new GitHub repo) with **only** this tree, set `origin`, and stop implying it is a “child” of another repo unless you **choose** to sync manually. |

## 2. Issues sorted (how I see them)

### A. **Solid — verified in this tree**

- **Lean:** `lake build` succeeds; double-slit stack, measurement channel, Landauer (`LandauerBound` + vendored `LandauerLaw` / extension / Einstein bridge), complementarity, Epistemic\* modules, `MeasurementCost.lean`, vendored **`Gate` → `MonoidalState`** chain, etc.
- **Haskell:** `cabal test` passes; QuickCheck mirrors core ideas + `MeasurementCost` + **`LandauerExtension`** + **`MonoidalState`** + **`landauer-einstein-sanity`**.
- **Coq / Agda (optional):** `make coq-check` / `make agda-check` on vendored slim files.
- **Python:** toy + Kraus + plots; 1D/2D Schrödinger starters; absorbing + complex edge mask; QuTiP parity scripts; benchmark; sparse FD smoke; tests under `sim/tests/`.
- **CI:** GitHub Actions for Lean+Python and Haskell; **path filters** to skip unrelated edits.

*You are not “missing” these — they are real files here.*

### B. **Open — explicitly still work (this repo)**

| Priority | Item | Notes |
|----------|------|--------|
| **Formal** | **`p3-epistemic-sensing`** | Connect ODE/PPO/runtime evidence to existing `Epistemic*` lemmas — not finished as “evidence story”. |
| **Formal** | **Richer `InfoEntropy`**, concrete **erasure vs Landauer** (beyond `LandauerBound` + vendored `LandauerLaw`) | Listed in `TODO-TRACKING.md` as next Lean depth. |
| **Python (optional)** | **PML / stretched coords**, **QuTiP on same sparse H** as `schrodinger_2d_sparse_fd_expm_smoke.py` | Roadmap, not required for correctness of current proofs. |
| **Cross-formalism** | **Full A0 Coq / Agda parity** | **`Coq/`** and **`Agda/`** exist but are **minimal** (Landauer–Einstein bridge + trace stub). Growing them to match parent `Gate` / `MonoidalState` / … is future work. |

### C. **Earlier scope mix-up (resolved by vendoring)**

Cross-lang artifacts **`LandauerExtension`**, **`FiberedActivation`**, **`MonoidalState`**, and the **ℚ `Gate` chain** are now **on disk in this repo** (copied from parent `umst-formal`). **`PARALLEL_WORK.md`** marks them **DONE** here.  

When parent Lean/Coq changes, **re-diff and re-sync** the vendored files (see root **`README.md` § *Vendored from parent*).

### D. **Housekeeping (low urgency)**

- Re-paste **`make lean-stats-md`** into **`PROOF-STATUS.md`** after big Lean edits.
- If **branch protection** requires CI on **every** PR, **path filters** skip jobs on docs-only PRs — widen `paths` or add `workflow_dispatch` if that bites you.

## 3. “Can this be a separate repo?” — **Yes**

It **already can be** treated as standalone:

1. **Create** a new empty repo on GitHub (or keep only this folder’s history).
2. **`git remote`** → point `origin` at that repo; push `main`.
3. **Update README** opening line if you like: drop “extension fork” and say **“standalone UMST double-slit formal + sim bundle”** (optional wording).
4. **Parent `umst-formal`:** only matters if you **port** lemmas by hand or use **git subtree/submodule** — not required for CI or for “this repo is complete on its own terms.”

**Pros of separate repo:** clear boundaries, own issues/CI, no confusion with “what’s in parent”.  
**Cons:** you duplicate or manually sync any Lean you want from parent; no automatic merge from upstream unless you set that up.

## 4. What to read next

- **Swarm / parallel work:** `Docs/PARALLEL_WORK.md`
- **Milestones vs editor todos:** `Docs/TODO-TRACKING.md`
- **Sim roadmap:** `sim/README.md`

**Single rule of thumb:** If **`glob`** / file search **doesn’t find it under this directory**, it’s **not part of this repo’s deliverable** until someone adds it — regardless of what another repo calls “done.”
