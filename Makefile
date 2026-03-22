# umst-formal-double-slit — local verification
.PHONY: lean lean-clean lean-stats lean-stats-md sim sim-test sim-gifs sim-gifs-validate telemetry-sample haskell-test coq-check agda-check formal-check ci-local ci-full

lean:
	cd Lean && lake build

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
# Coq: Rocq/Coq 9.x or 8.20+ with `From Stdlib` layout. Order respects module imports.
COQ_VO := LandauerEinsteinBridge.v DensityStateSpec.v ComplementaritySpec.v VonNeumannEntropySpec.v \
	MeasurementCost.v InfoTheory.v Gate.v Extraction.v Constitutional.v

coq-check:
	@set -e; cd Coq; for f in $(COQ_VO); do coqc -Q . UMSTFormal "$$f"; done

# Agda: 2.6+ stdlib; order respects local `open import` dependencies.
AGDA_MAIN := DensityStateSpec.agda ComplementaritySpec.agda VonNeumannEntropySpec.agda \
	LandauerEinsteinTrace.agda Gate.agda Helmholtz.agda DIB-Kleisli.agda Naturality.agda \
	Activation.agda InfoTheory.agda MeasurementCost.agda

agda-check:
	@set -e; cd Agda; for f in $(AGDA_MAIN); do agda -v0 "$$f"; done

# Single entry point for formal verification tracks (Coq + Agda).
formal-check: coq-check agda-check

# CI: after `lake build`, `.github/workflows/lean.yml` runs `pip install -r sim/requirements-optional.txt`,
# then the same commands as `make sim` plus `unittest` (same as `make sim-test`) and `sim-gifs-validate`.
# Local `make ci-local` does not pip-install; QuTiP tests skip unless you install optional deps.
# `.github/workflows/haskell.yml` runs `cabal test` separately (not part of ci-local).
# Optional: Lean + Python + Haskell in one go (requires cabal/GHC).
ci-local: lean sim sim-test

ci-full: ci-local haskell-test
