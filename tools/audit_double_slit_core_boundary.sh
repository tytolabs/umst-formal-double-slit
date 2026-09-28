#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
#
# P0-11 — DoubleSlitCore fibre boundary audit (measured grep, not physics GREEN).
# DoubleSlitCore may open UMST.Core scalar/state vocabulary only.
# Density-matrix → ObservationState maps live in QuantumClassicalBridge, not here.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CORE="${ROOT}/Lean/DoubleSlitCore.lean"

if [[ ! -f "${CORE}" ]]; then
  echo "audit_double_slit_core_boundary: missing ${CORE}" >&2
  exit 1
fi

code_lines() {
  awk '
    /^import / { print; next }
    /^[[:space:]]*(def|theorem|lemma|instance|structure|abbrev|noncomputable def|class) / { print; next }
  ' "${CORE}"
}

if grep -E '^import (DensityState|DensityMatrix|QuantumClassicalBridge|Concrete\.|Concrete/)' "${CORE}"; then
  echo "audit_double_slit_core_boundary: forbidden import in DoubleSlitCore.lean" >&2
  exit 1
fi

if code_lines | grep -E '(DensityMatrix|ConcreteState|observationState(Canonical|Of))'; then
  echo "audit_double_slit_core_boundary: forbidden density-matrix / ConcreteState map in code" >&2
  exit 1
fi

grep -q 'import Core.State' "${CORE}" || {
  echo "audit_double_slit_core_boundary: missing import Core.State" >&2
  exit 1
}

grep -q 'open UMST.Core' "${CORE}" || {
  echo "audit_double_slit_core_boundary: missing open UMST.Core" >&2
  exit 1
}

grep -q 'ThermodynamicSystem' "${CORE}" || {
  echo "audit_double_slit_core_boundary: missing ThermodynamicSystem instance" >&2
  exit 1
}

exit 0
