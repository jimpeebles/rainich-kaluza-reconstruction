"""Deterministic provenance hashes for exact validation artifacts.

The benchmark ``input_sha256`` fields intentionally identify the compact,
human-readable input manifests.  They do not identify the implementation or
the full symbolic model.  This module supplies those two additional hashes so
artifacts can distinguish all three scopes explicitly.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
from typing import Iterable

import sympy as sp


VALIDATION_ROOT = Path(__file__).resolve().parents[1]


def symbolic_model_sha256(expressions: Iterable[object]) -> str:
    """Hash canonical SymPy expression trees, including matrix shape."""

    payload: list[str] = []
    for value in expressions:
        if isinstance(value, sp.MatrixBase):
            payload.append(f"matrix:{value.rows}:{value.cols}")
            payload.extend(sp.srepr(entry) for entry in value)
        elif isinstance(value, (tuple, list)):
            payload.append(f"sequence:{len(value)}")
            payload.extend(sp.srepr(sp.sympify(entry)) for entry in value)
        else:
            payload.append(sp.srepr(sp.sympify(value)))
    return hashlib.sha256("\n".join(payload).encode("utf-8")).hexdigest()


def implementation_sha256(relative_paths: Iterable[str]) -> str:
    """Hash named validation sources together with their relative paths."""

    digest = hashlib.sha256()
    for relative_path in sorted(relative_paths):
        path = VALIDATION_ROOT / relative_path
        data = path.read_bytes()
        encoded_path = relative_path.encode("utf-8")
        digest.update(len(encoded_path).to_bytes(8, "big"))
        digest.update(encoded_path)
        digest.update(len(data).to_bytes(8, "big"))
        digest.update(data)
    return digest.hexdigest()
