# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

"""Tests for sim/telemetry_trace_consumer.py (Gap 14 — Lean-aligned epistemic fields)."""

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "sim" / "telemetry_trace_consumer.py"


def _load_consumer():
    name = "telemetry_trace_consumer"
    spec = importlib.util.spec_from_file_location(name, SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


class TelemetryTraceConsumerTests(unittest.TestCase):
    def test_epistemic_aliases_pass(self):
        c = _load_consumer()
        T = 300.0
        k_b = 1.380649e-23
        mi = 0.25 * np.log(2.0)
        cost = k_b * T * mi
        trace = {
            "steps": [
                {
                    "trajMI": mi,
                    "effortCost": cost,
                    "temperature": T,
                }
            ]
        }
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
            json.dump(trace, tmp)
            path = Path(tmp.name)
        try:
            results = c.consume_trace(path, 1e-9)
            names = [r.name for r in results]
            self.assertIn("step[0].EpistemicMI_nats", names)
            self.assertIn("step[0].EpistemicLandauerCost", names)
            self.assertIn("step[0].EpistemicCostMI_consistency", names)
            self.assertTrue(all(r.passed for r in results))
        finally:
            path.unlink(missing_ok=True)

    def test_epistemic_mi_exceeds_ln2_fails(self):
        c = _load_consumer()
        trace = {"steps": [{"stepMI": np.log(2.0) + 0.01, "temperature": 300.0}]}
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
            json.dump(trace, tmp)
            path = Path(tmp.name)
        try:
            results = c.consume_trace(path, 1e-9)
            mi_results = [r for r in results if "EpistemicMI_nats" in r.name]
            self.assertEqual(len(mi_results), 1)
            self.assertFalse(mi_results[0].passed)
        finally:
            path.unlink(missing_ok=True)

    def test_aggregate_catalog_and_fold(self):
        c = _load_consumer()
        T = 300.0
        k_b = 1.380649e-23
        mi1 = 0.1 * np.log(2.0)
        mi2 = 0.2 * np.log(2.0)
        c1 = k_b * T * mi1
        c2 = k_b * T * mi2
        trace = {
            "temperature": T,
            "steps": [
                {"trajMI": mi1, "effortCost": c1, "temperature": T},
                {"trajMI": mi2, "effortCost": c2, "temperature": T},
            ],
            "aggregate": {
                "aggregateMI": mi1 + mi2,
                "aggregateCost": c1 + c2,
            },
        }
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
            json.dump(trace, tmp)
            path = Path(tmp.name)
        try:
            results = c.consume_trace(path, 1e-9)
            names = [r.name for r in results]
            self.assertIn("EpistemicAggregateMI_catalog", names)
            self.assertIn("EpistemicAggregateCost_catalog", names)
            self.assertIn("EpistemicFold_sumMI", names)
            self.assertIn("EpistemicFold_sumCost", names)
            self.assertTrue(all(r.passed for r in results))
        finally:
            path.unlink(missing_ok=True)

    def test_aggregate_with_partial_steps_fails_fold_gate(self):
        c = _load_consumer()
        T = 300.0
        k_b = 1.380649e-23
        mi = 0.15 * np.log(2.0)
        cost = k_b * T * mi
        trace = {
            "temperature": T,
            "steps": [
                {"trajMI": mi, "effortCost": cost},
                {"visibility": 1.0, "distinguishability": 0.0},
            ],
            "aggregateMI": mi,
            "aggregateCost": cost,
        }
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
            json.dump(trace, tmp)
            path = Path(tmp.name)
        try:
            results = c.consume_trace(path, 1e-9)
            fold = [r for r in results if r.name == "EpistemicFold_skipped"]
            self.assertEqual(len(fold), 1)
            self.assertFalse(fold[0].passed)
        finally:
            path.unlink(missing_ok=True)

    def test_emitted_block_metadata_and_mi(self):
        c = _load_consumer()
        T = 300.0
        k_b = 1.380649e-23
        mi = 0.2 * np.log(2.0)
        cost = k_b * T * mi
        trace = {
            "steps": [
                {
                    "emitted": {
                        "stepMI": mi,
                        "stepCost": cost,
                        "thermodynamicAdmissible": True,
                        "confidence": 0.95,
                    },
                    "temperature": T,
                }
            ]
        }
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
            json.dump(trace, tmp)
            path = Path(tmp.name)
        try:
            results = c.consume_trace(path, 1e-9)
            names = [r.name for r in results]
            self.assertIn("step[0].EmittedStep_confidence", names)
            self.assertIn("step[0].EmittedStep_thermodynamicAdmissible", names)
            self.assertTrue(all(r.passed for r in results))
        finally:
            path.unlink(missing_ok=True)

    def test_emitted_confidence_out_of_range_fails(self):
        c = _load_consumer()
        trace = {"steps": [{"confidence": 1.5}]}
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
            json.dump(trace, tmp)
            path = Path(tmp.name)
        try:
            results = c.consume_trace(path, 1e-9)
            conf = [r for r in results if "EmittedStep_confidence" in r.name]
            self.assertEqual(len(conf), 1)
            self.assertFalse(conf[0].passed)
        finally:
            path.unlink(missing_ok=True)

    def test_sim_lean_bridge_only_still_passes(self):
        c = _load_consumer()
        trace = {
            "steps": [
                {
                    "density_matrix_real": [[0.5, 0], [0, 0.5]],
                    "density_matrix_imag": [[0, 0], [0, 0]],
                    "path_weights": [0.5, 0.5],
                    "visibility": 0.0,
                    "distinguishability": 0.0,
                    "entropy_bits": 1.0,
                    "temperature": 300.0,
                }
            ]
        }
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
            json.dump(trace, tmp)
            path = Path(tmp.name)
        try:
            results = c.consume_trace(path, 1e-6)
            self.assertTrue(all(r.passed for r in results))
        finally:
            path.unlink(missing_ok=True)


if __name__ == "__main__":
    unittest.main()
