# umst-formal-double-slit — local verification
.PHONY: lean lean-clean lean-stats lean-stats-md sim sim-test haskell-test coq-check agda-check ci-local ci-full

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

# Optional: QuickCheck mirror (requires GHC/cabal). See Haskell/README.md.
haskell-test:
	cd Haskell && cabal test

# Optional: integrated Coq/Agda from upstream framework (requires coqc / agda on PATH).
coq-check:
	cd Coq && coqc -Q . UMSTFormal LandauerEinsteinBridge.v

agda-check:
	cd Agda && agda -v0 LandauerEinsteinTrace.agda

# CI: after `lake build`, `.github/workflows/lean.yml` runs `pip install -r sim/requirements-optional.txt`,
# then the same commands as `make sim` plus `unittest` (same as `make sim-test`).
# Local `make ci-local` does not pip-install; QuTiP tests skip unless you install optional deps.
# `.github/workflows/haskell.yml` runs `cabal test` separately (not part of ci-local).
# Optional: Lean + Python + Haskell in one go (requires cabal/GHC).
ci-local: lean sim sim-test

ci-full: ci-local haskell-test
