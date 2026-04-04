"""Load adoption / growth JSON series validated against `data/schemas/adoption_growth_series.schema.json`."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def load_series(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    for k in ("source_id", "unit", "points"):
        if k not in data:
            raise ValueError(f"missing {k}")
    return data


def to_numpy(data: dict[str, Any]) -> tuple[list[str], list[float]]:
    pts = data["points"]
    ts = [str(p["t"]) for p in pts]
    ys = [float(p["y"]) for p in pts]
    return ts, ys
