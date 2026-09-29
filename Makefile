# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
# umst-formal-double-slit — local verification
.PHONY: lean lean-clean lean-catalog-export lean-stats lean-stats-md sim sim-test sim-gifs sim-gifs-validate telemetry-sample haskell-test coq-check agda-check formal-check ci-local ci-full

lean:
	cd Lean && lake build

# Emit `artifacts/catalog.json` + `artifacts/catalog.lock.json` (see `artifacts/README.md`).
lean-catalog-export:
	APPROVE_CROSS_REPO_MERGE=1 python3 tools/lean_export/export_catalog.py \
		--lean-root Lean \
		--also-lean-root ../umst-formal/Lean \
		--also-lean-repo-tag umst-formal \
		--out artifacts/catalog.json

lean-clean:
	cd Lean && lake clean

# Heuristic declaration counts for docs (excludes Lean/.lake).
lean-stats:
	python3 scripts/lean_decl_stats.py

lean-stats-md:
	python3 scripts/lean_decl_stats.py --markdown

sim:
	python3 sim/toy_double_slit_mi_gate.py --validate
	python3 sim/plot_toy_complementarity_svg.py --validate
	python3 sim/qubit_kraus_sweep.py --validate
	python3 sim/plot_complementarity_svg.py --validate

sim-test:
	python3 -m unittest discover -s sim/tests -p "test_*.py"

# Optional: wave simulation GIFs (matplotlib + imageio; see scripts/generate_sim_gifs.py).
sim-gifs:
	python3 scripts/generate_sim_gifs.py

sim-gifs-validate:
	python3 scripts/generate_sim_gifs.py --validate

# Gap 14: golden Lean-aligned telemetry JSON + run consumer (requires NumPy).
telemetry-sample:
	python3 sim/export_sample_telemetry_trace.py --validate

# Optional: QuickCheck mirror (requires GHC/cabal). See Haskell/README.md.
haskell-test:
	cd Haskell && cabal test

# Optional: integrated Coq/Agda (requires `coqc` / `agda` on PATH).
.PHONY: coq-check agda-check formal-check

coq-check:
	$(MAKE) -C Coq -f Makefile.coq clean
	$(MAKE) -C Coq -f Makefile.coq all

# Agda: 2.6+ stdlib; order respects local `open import` dependencies.
AGDA_FLAGS := --include-path=. -l standard-library -W noLibUnknownField
AGDA_MAIN := DensityStateSpec.agda ComplementaritySpec.agda \
	LandauerEinsteinTrace.agda Gate.agda Helmholtz.agda DIB-Kleisli.agda Naturality.agda \
	Activation.agda InfoTheory.agda MeasurementCost.agda

agda-check:
	@set -e; cd Agda; rm -f *.agdai; for f in $(AGDA_MAIN); do agda $(AGDA_FLAGS) -v0 "$$f"; done

# Single entry point for formal verification tracks (Coq + Agda).
formal-check: coq-check agda-check

# CI: after `lake build`, `.github/workflows/lean.yml` runs `pip install -r sim/requirements-optional.txt`
# (includes `sim/requirements.txt`: numpy + pydantic), then the same commands as `make sim` plus unittest.
# Local `make ci-local` does not pip-install: run `pip install -r sim/requirements.txt` for telemetry + NumPy
# tests, or `pip install -r sim/requirements-optional.txt` for QuTiP / matplotlib / SciPy as well.
# `.github/workflows/haskell.yml` runs `cabal test` separately (not part of ci-local).
# Optional: Lean + Python + Haskell in one go (requires cabal/GHC).
ci-local: lean sim sim-test

ci-full: ci-local haskell-test
