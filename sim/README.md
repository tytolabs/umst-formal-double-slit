<!--
SPDX-License-Identifier: MIT
Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO
-->

# Simulation quickstart

This folder contains lightweight Python simulation utilities for the double-slit extension.

## Roadmap (Python)

| Priority | Item | Status |
|----------|------|--------|
| 1 | Stdlib toy + **toy complementarity SVG** (`plot_toy_complementarity_svg.py`) + qubit Kraus + qubit SVG (`plot_complementarity_svg.py`) | **In repo** — runs in `make sim` / CI |
| 2 | **QuTiP** parity — qubit (`qutip_qubit_kraus.py`, `test_qutip_parity.py`); **2D free** + **2D soft slit** (`qutip_schrodinger_2d_*_parity.py`, `test_qutip_2d_*_parity.py`) + **`sim/requirements-optional.txt`** | **CI:** GHA installs optional deps then runs full unittest. **Local:** `pip install -r sim/requirements-optional.txt` or tests skip |
| 3 | **Matplotlib / GIF** (toy script `--plot`, `--generate-gif`) | **In repo** — needs deps from `requirements-optional.txt`; not part of default `make sim` |
| 4 | Spatial Schrödinger / full QuTiP dynamics | **Starters:** as above + **2D real sponge** + **complex edge mask** + **sparse FD `expm_multiply` smoke** (`schrodinger_2d_sparse_fd_expm_smoke.py`, SciPy) + **QuTiP** 2D parity + **benchmark** (`benchmark_schrodinger_2d_split_step_vs_fd.py`). **Open:** true PML / stretched coords, large-grid QuTiP on sparse **H**, reference ABC checks |

## Toy simulator

Run from repo root:

```bash
make sim
```

Or directly:

```bash
python3 sim/toy_double_slit_mi_gate.py --validate
```

Default output:

- `sim/out/results_double_slit_toy.csv`
- After `make sim`: `sim/out/complementarity_toy_sweep.svg` (reads the toy CSV; stdlib only)

Optional summary output:

```bash
python3 sim/toy_double_slit_mi_gate.py \
  --summary-csv sim/out/summary_double_slit_toy.csv
```

Optional **matplotlib** PNG / **GIF** (requires `pip install -r sim/requirements-optional.txt`):

```bash
python3 sim/toy_double_slit_mi_gate.py --validate --plot
python3 sim/toy_double_slit_mi_gate.py --validate --generate-gif
```

CI runs `sim/tests/test_toy_matplotlib_smoke.py` and `sim/tests/test_toy_gif_smoke.py` when optional deps import successfully.

## Qubit Kraus sweep (Lean-aligned metrics)

No third-party deps. Applies identity vs Lüders which-path Kraus maps to `|+⟩`, `|0⟩`, `|1⟩` and reports `pathWeight`, `V`, `I`, `V²+I²` (same definitions as `QuantumClassicalBridge`).

```bash
python3 sim/qubit_kraus_sweep.py --validate
```

Default CSV: `sim/out/qubit_kraus_sweep.csv`.

## Complementarity figure (SVG, stdlib)

Reads the qubit sweep CSV and writes a quarter-disk `V²+I²≤1` diagram with labeled points.

```bash
python3 sim/plot_complementarity_svg.py --validate
```

Default output: `sim/out/complementarity_qubit_sweep.svg`.

## Free 1D Gaussian (closed form)

Illustrative **spatial** density |ψ(x,t)|² for a freely spreading minimum-uncertainty packet (stdlib only). Not wired into default `make sim`; covered by `unittest` and safe to extend toward numerical propagation later.

```bash
python3 sim/spatial_free_gaussian_1d.py --validate
```

Writes `sim/out/spatial_free_gaussian.csv` by default.

**SVG:** stdlib plotter (computed samples or optional `--in` CSV):

```bash
python3 sim/plot_spatial_free_gaussian_svg.py --validate
```

Default output: `sim/out/spatial_free_gaussian.svg`.

## Free 1D Schrödinger on a grid (FFT, NumPy)

Periodic box, **V = 0**: evolve ψ with FFT kinetic propagator; **`--validate`** compares |ψ|² to `spatial_free_gaussian_1d.py`. Requires **NumPy** (`requirements-optional.txt`).

```bash
python3 sim/schrodinger_1d_free_fft.py --validate
```

Not in default `make sim`; `unittest` runs when NumPy is installed (CI after `pip install -r sim/requirements-optional.txt`).

## Split-step + soft barrier (NumPy)

Strang splitting **K(dt/2) V K(dt/2)** on the same periodic grid. **`--validate --v0 0`** checks against `schrodinger_1d_free_fft`; with **`--v0 > 0`** runs a Gaussian barrier unitarity smoke.

```bash
python3 sim/schrodinger_1d_split_step.py --validate --v0 0
python3 sim/schrodinger_1d_split_step.py --validate --v0 18
```

Writes `sim/out/schrodinger_split_step_rho.csv` by default.

**SVG (stdlib):**

```bash
python3 sim/plot_schrodinger_split_step_svg.py --validate
```

Default: `sim/out/schrodinger_split_step.svg` (needs the CSV above).

## Absorbing edges (NumPy, pedagogical sponge)

After each Strang step, ψ is multiplied by a symmetric taper (**η** at the outermost cells, **1** in the bulk). Not a perfect ABC; use for finite-grid outgoing waves. **`--validate`** checks `n_absorb=0` ≡ plain split-step and an **edge-localized** packet loses norm.

```bash
python3 sim/schrodinger_1d_absorbing_edges.py --validate
```

Writes `sim/out/schrodinger_absorbing_edges_rho.csv`.

**SVG (stdlib):**

```bash
python3 sim/plot_schrodinger_absorbing_edges_svg.py --validate
```

Default: `sim/out/schrodinger_absorbing_edges.svg` (needs the CSV above).

## Soft double-slit screen (1D caricature, NumPy)

High plateau for `x ≥ x_screen` with two Gaussian openings; incoming Gaussian from the left. **`--validate`** checks norm and a coarse fringe-count heuristic on `ρ` past the screen.

```bash
python3 sim/schrodinger_1d_soft_double_slit.py --validate
```

Writes `sim/out/schrodinger_soft_double_slit_rho.csv` (`x`, `V`, `ρ`).

**SVG (stdlib):** reads that CSV (or `--in` path) and plots **ρ** + scaled **V**:

```bash
python3 sim/plot_schrodinger_soft_double_slit_svg.py --validate
```

Default output: `sim/out/schrodinger_soft_double_slit.svg` (requires CSV from the step above).

## Soft double-slit screen (2D, NumPy)

True 2D periodic box: separable incoming Gaussian, vertical soft screen at `x ≥ x_screen` with two openings in **y**. **`--validate --v0 0`** checks split-step against one-shot **2D FFT**; with **`--v0 > 0`**, norm smoke.

```bash
python3 sim/schrodinger_2d_soft_double_slit.py --validate --v0 0 --nx 64 --ny 64 --lx 32 --ly 32 --steps 80 --t 0.5
python3 sim/schrodinger_2d_soft_double_slit.py --validate
```

Writes `sim/out/schrodinger_2d_soft_double_slit_rho.csv` (`x`, `y`, `ρ`), one row per grid point (default grid is moderately sized; adjust `--nx`/`--ny`).

**SVG heatmap (stdlib):**

```bash
python3 sim/plot_schrodinger_2d_soft_double_slit_svg.py --validate --stride 2
```

Default: `sim/out/schrodinger_2d_soft_double_slit.svg`. Use **`--stride N`** to coarsen large grids.

## Benchmark: 2D split-step vs FD + expm (optional)

Compares **FFT split-step** evolution to a **dense FD** Hamiltonian + **`scipy.linalg.expm`** (small grids). Prints **wall time** for each path and **max relative** ``|ρ_ss - ρ_fd|``. Use **`--json`** for machine-readable output.

```bash
python3 sim/benchmark_schrodinger_2d_split_step_vs_fd.py --nx 20 --ny 20 --steps 50
python3 sim/benchmark_schrodinger_2d_split_step_vs_fd.py --json
```

**Requires** SciPy (e.g. via `pip install -r sim/requirements-optional.txt`). `sim/tests/test_benchmark_schrodinger_2d_split_step_vs_fd.py` skips if SciPy is missing.

## Sparse FD Hamiltonian + `expm_multiply` (optional)

Builds the **same** periodic FD **H** (kinetic + soft slit **V**) as **`qutip_schrodinger_2d_slit_parity`**, but as **SciPy CSR**; compares **`scipy.sparse.linalg.expm_multiply(-i H t, ψ)`** to dense **`expm`** on a **small** grid (hook for large-**N** workflows).

```bash
python3 sim/schrodinger_2d_sparse_fd_expm_smoke.py
```

**Requires** SciPy. `sim/tests/test_schrodinger_2d_sparse_fd_expm_smoke.py` skips without `scipy.sparse`.

## QuTiP 2D free parity (optional)

Dense **periodic finite-difference** Laplacian on an `nx × ny` grid; compares **`qutip.sesolve`** to **`scipy.linalg.expm(-1j H t)`** on the **same** Hamiltonian (initial Gaussian aligned with `schrodinger_2d_soft_double_slit`). Optional **`--spectral-gap`** prints how far **FFT** vs **FD** densities differ (diagnostic only).

```bash
python3 sim/qutip_schrodinger_2d_free_parity.py
python3 sim/qutip_schrodinger_2d_free_parity.py --spectral-gap
```

**Requires** `qutip` + `scipy`. Covered by `sim/tests/test_qutip_2d_free_parity.py` when installed.

## QuTiP 2D soft-slit parity (optional)

Same **FD kinetic** as the free script, plus **diagonal** potential from **`soft_double_slit_potential_2d`** on the tensor grid (values match NumPy’s discrete **V**). Compares **`qutip.sesolve`** vs **`scipy.linalg.expm`** on that **H**. This is **not** identical to NumPy **split-step FFT** evolution; optional **`--diagnostic-ss-fd`** prints a relative **ρ** gap between split-step and FD one-shot.

```bash
python3 sim/qutip_schrodinger_2d_slit_parity.py
python3 sim/qutip_schrodinger_2d_slit_parity.py --diagnostic-ss-fd
```

**Requires** `qutip` + `scipy`. Covered by `sim/tests/test_qutip_2d_slit_parity.py` when installed.

## 2D soft slit + absorbing sponge (NumPy)

Same **soft double-slit** potential as **`schrodinger_2d_soft_double_slit.py`**, but after each Strang step ψ is multiplied by a **separable** edge taper (`m_x[i] m_y[j]`, same 1D taper as **`schrodinger_1d_absorbing_edges.py`**). **`--validate`**: zero sponge ≡ plain 2D split-step; **corner-localized** packet shows norm drop.

```bash
python3 sim/schrodinger_2d_absorbing_edges.py --validate
```

Writes `sim/out/schrodinger_2d_absorbing_edges_rho.csv` (`x`, `y`, `ρ`). **Heatmap:** reuse the 2D plotter:

```bash
python3 sim/plot_schrodinger_2d_soft_double_slit_svg.py --in sim/out/schrodinger_2d_absorbing_edges_rho.csv --out sim/out/schrodinger_2d_absorbing_edges.svg --validate --stride 2
```

## 2D complex edge mask (PML caricature, NumPy)

Same real **taper** as the sponge, multiplied by **separable** ``e^{i φ}`` with linear **φ** in the absorb strips (``--kappa-x``, ``--kappa-y``). **|mask| = m_x m_y** (same attenuation as real sponge); phase is pedagogical, not full PML. **`--validate`**: **κ = 0** matches **`schrodinger_2d_absorbing_edges`**; corner packet norm drop with **κ > 0**.

```bash
python3 sim/schrodinger_2d_complex_absorb_mask.py --validate
```

Writes `sim/out/schrodinger_2d_complex_absorb_mask_rho.csv`. Heatmap: same 2D plotter with `--in` / `--out`.

## Classical Fraunhofer double slit

Far-field intensity I(θ) ∝ sinc²(π a sinθ/λ) cos²(π d sinθ/λ), normalized to I(0)=1 (stdlib).

```bash
python3 sim/classical_double_slit_far_field.py --validate
```

Default CSV: `sim/out/classical_double_slit_far_field.csv`. Not part of default `make sim`; unittest covers it.

**SVG:** stdlib plotter (computed curve or optional `--in` CSV):

```bash
python3 sim/plot_classical_double_slit_svg.py --validate
```

Default output: `sim/out/classical_double_slit_far_field.svg`.

## Telemetry trace consumer (Gap 14)

[`telemetry_trace_consumer.py`](telemetry_trace_consumer.py) validates JSON traces against **`SimLeanBridge`**
-style fields (density matrix, path weights, complementarity, diagonal entropy bits) and, optionally,
**epistemic** per-step fields aligned with **`EpistemicTelemetryBridge`** / **`EmittedTraceSchema`**:

- `stepMI` or `trajMI` — MI surrogate in **nats** (`0 … ln 2`).
- `stepCost` or `effortCost` — joules, capped by `k_B T ln 2` at `temperature` (default 300 K).
- Optional root **`aggregateMI`** / **`aggregateCost`** (or nested **`aggregate`** object) — catalog bounds vs `n` steps; if every step has MI+cost, **sum vs aggregate** fold checks.
- Optional **`thermodynamicAdmissible`** / **`confidence`** per step (flat or nested **`emitted`**) — matches Lean **`EmittedStepRecord`** / **`EmittedTraceWellFormed`**.

```bash
python3 sim/telemetry_trace_consumer.py your_trace.json
python3 -m unittest sim.tests.test_telemetry_trace_consumer -v
```

**Golden producer (Lean-aligned qubit trace):** [`export_sample_telemetry_trace.py`](export_sample_telemetry_trace.py) writes `sim/out/sample_lean_aligned_telemetry.json` by default (diagonal Shannon nats = `whichPathMI` story, `k_B T MI` costs, nested `emitted`, root `aggregate`). Requires **NumPy**.

```bash
python3 sim/export_sample_telemetry_trace.py --validate
```

## Optional dependencies (`requirements-optional.txt`)

Bundled for **NumPy** (FFT sim), **QuTiP parity**, **matplotlib**, and **imageio** (GIF). GitHub Actions installs this file before `unittest`, so NumPy/QuTiP tests run in CI when the install succeeds.

```bash
pip install -r sim/requirements-optional.txt
python3 -m unittest discover -s sim/tests -p "test_*.py"
```

Without those packages, **`test_qutip_parity`**, **`test_qutip_2d_free_parity`**, **`test_qutip_2d_slit_parity`**, **`test_schrodinger_2d_sparse_fd_expm_smoke`** (and matplotlib/GIF paths) are skipped or print install hints.

## Local simulator tests

Run:

```bash
make sim-test
make telemetry-sample   # Gap 14 — export golden trace + consumer (NumPy); same step as CI after unittests
```
