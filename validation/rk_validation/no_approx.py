"""Reject approximate scientific arithmetic in the exact validation suite."""

from __future__ import annotations

import ast
from pathlib import Path


VALIDATION_ROOT = Path(__file__).resolve().parents[1]
SCANNED_DIRECTORIES = ("rk_validation", "benchmarks", "tests")
BANNED_IMPORT_ROOTS = {"cmath", "math", "mpmath", "numpy", "scipy"}
BANNED_CALL_NAMES = {"N", "evalf", "float", "isclose", "n", "nsimplify"}


def _call_name(function: ast.expr) -> str | None:
    if isinstance(function, ast.Name):
        return function.id
    if isinstance(function, ast.Attribute):
        return function.attr
    return None


def audit_file(path: Path) -> list[str]:
    """Return source-located violations for one Python file."""

    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    relative = path.relative_to(VALIDATION_ROOT)
    violations: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            violations.append(f"{relative}:{node.lineno}: floating-point literal")
        elif isinstance(node, ast.Import):
            for alias in node.names:
                root = alias.name.split(".", 1)[0]
                if root in BANNED_IMPORT_ROOTS:
                    violations.append(
                        f"{relative}:{node.lineno}: prohibited approximate import {root}"
                    )
        elif isinstance(node, ast.ImportFrom) and node.module:
            root = node.module.split(".", 1)[0]
            if root in BANNED_IMPORT_ROOTS:
                violations.append(
                    f"{relative}:{node.lineno}: prohibited approximate import {root}"
                )
        elif isinstance(node, ast.Call):
            name = _call_name(node.func)
            if name in BANNED_CALL_NAMES:
                violations.append(
                    f"{relative}:{node.lineno}: prohibited approximate call {name}"
                )
    return violations


def main() -> None:
    violations: list[str] = []
    for directory in SCANNED_DIRECTORIES:
        for path in sorted((VALIDATION_ROOT / directory).rglob("*.py")):
            violations.extend(audit_file(path))
    if violations:
        raise SystemExit("\n".join(violations))
    print("PASS exact-arithmetic AST audit")


if __name__ == "__main__":
    main()
