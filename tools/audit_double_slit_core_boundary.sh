#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
#
# P0-11b — knowing fibre boundary audit (all double-slit Lean sources).

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN_DIR="${ROOT}/Lean"

if [[ ! -d "${LEAN_DIR}" ]]; then
  echo "audit_double_slit_core_boundary: missing ${LEAN_DIR}" >&2
  exit 1
fi

while IFS= read -r f; do
  rel="${f#"${ROOT}/"}"
  if grep -E '^import (Concrete\.|Concrete/)' "${f}"; then
    echo "audit_double_slit_core_boundary: forbidden acting Concrete import in ${rel}" >&2
    exit 1
  fi
  if grep -F 'noncomputable def thermoFromQubitPath' "${f}"; then
    echo "audit_double_slit_core_boundary: forbidden thermoFromQubitPath in ${rel}" >&2
    exit 1
  fi
  if grep -F 'noncomputable def thermoCalibratedScaffold' "${f}"; then
    echo "audit_double_slit_core_boundary: forbidden thermoCalibratedScaffold in ${rel}" >&2
    exit 1
  fi
  if grep -F 'noncomputable def thermoCalibratedPhys' "${f}"; then
    echo "audit_double_slit_core_boundary: forbidden thermoCalibratedPhys in ${rel}" >&2
    exit 1
  fi
  hit="$(awk '
    /^import / { next }
    /^[[:space:]]*--/ { next }
    /^[[:space:]]*\/-/ { next }
    /noncomputable def|^def |^theorem |^lemma / {
      if ($0 ~ /DensityMatrix/ && $0 ~ /RealThermodynamicState/ && $0 ~ /→/) { print; exit }
      if ($0 ~ /DensityMatrix/ && $0 ~ /ConcreteState/ && $0 ~ /→/) { print; exit }
    }
  ' "${f}" || true)"
  if [[ -n "${hit}" ]]; then
    echo "audit_double_slit_core_boundary: forbidden knowing→acting carrier in ${rel}: ${hit}" >&2
    exit 1
  fi
done < <(find "${LEAN_DIR}" -path '*/.lake' -prune -o -name '*.lean' -type f -print | sort)

CORE="${LEAN_DIR}/DoubleSlitCore.lean"
grep -q 'import Core.State' "${CORE}" || {
  echo "audit_double_slit_core_boundary: DoubleSlitCore missing import Core.State" >&2
  exit 1
}

grep -q 'open UMST.Core' "${CORE}" || {
  echo "audit_double_slit_core_boundary: DoubleSlitCore missing open UMST.Core" >&2
  exit 1
}

exit 0
