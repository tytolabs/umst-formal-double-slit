#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Santosh Prabhu Shenbagamoorthy and Santhosh Shyamsundar
# SPDX-License-Identifier: MIT
#
# Wrapper for `make formal-check` (Coq + Agda). Run from anywhere.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
exec make formal-check
