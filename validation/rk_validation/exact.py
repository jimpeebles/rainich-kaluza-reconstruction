"""Small exact-arithmetic tensor engine for Phase-V validation.

The implementation intentionally favors transparent coordinate formulas over
black-box differential-geometry helpers.  Every returned component is reduced
with SymPy's exact simplifier; no floating-point evaluation is used.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Sequence

import sympy as sp


Coordinates = Sequence[sp.Symbol]


def _square_matrix(metric: sp.MatrixBase, dimension: int) -> sp.ImmutableMatrix:
    matrix = sp.ImmutableMatrix(metric)
    if matrix.shape != (dimension, dimension):
        raise ValueError(
            f"metric shape {matrix.shape} does not match {dimension} coordinates"
        )
    if matrix != matrix.T:
        raise ValueError("metric must be symmetric")
    if sp.simplify(matrix.det()) == 0:
        raise ValueError("metric must be nondegenerate")
    return matrix


def simplify_matrix(matrix: sp.MatrixBase) -> sp.ImmutableMatrix:
    """Simplify every component while retaining an immutable exact matrix."""

    return sp.ImmutableMatrix(matrix.applyfunc(sp.simplify))


def matrix_is_zero(matrix: sp.MatrixBase) -> bool:
    """Decide componentwise exact vanishing after simplification."""

    return all(sp.simplify(component) == 0 for component in matrix)


def christoffel_symbols(
    coordinates: Coordinates, metric: sp.MatrixBase
) -> tuple[tuple[tuple[sp.Expr, ...], ...], ...]:
    """Return second-kind Christoffel symbols ``Gamma[k][i][j]``."""

    dimension = len(coordinates)
    covariant = _square_matrix(metric, dimension)
    inverse = simplify_matrix(covariant.inv())

    return tuple(
        tuple(
            tuple(
                sp.simplify(
                    sp.Rational(1, 2)
                    * sum(
                        inverse[k, ell]
                        * (
                            sp.diff(covariant[ell, j], coordinates[i])
                            + sp.diff(covariant[ell, i], coordinates[j])
                            - sp.diff(covariant[i, j], coordinates[ell])
                        )
                        for ell in range(dimension)
                    )
                )
                for j in range(dimension)
            )
            for i in range(dimension)
        )
        for k in range(dimension)
    )


def ricci_tensor(coordinates: Coordinates, metric: sp.MatrixBase) -> sp.ImmutableMatrix:
    """Compute ``R_ij`` from the coordinate Christoffel formula."""

    dimension = len(coordinates)
    gamma = christoffel_symbols(coordinates, metric)
    result = sp.MutableDenseMatrix.zeros(dimension, dimension)

    for i in range(dimension):
        for j in range(dimension):
            component = sp.S.Zero
            for k in range(dimension):
                component += sp.diff(gamma[k][i][j], coordinates[k])
                component -= sp.diff(gamma[k][i][k], coordinates[j])
                for ell in range(dimension):
                    component += gamma[k][i][j] * gamma[ell][k][ell]
                    component -= gamma[ell][i][k] * gamma[k][j][ell]
            result[i, j] = sp.simplify(component)

    return sp.ImmutableMatrix(result)


def scalar_curvature(coordinates: Coordinates, metric: sp.MatrixBase) -> sp.Expr:
    """Compute the exact scalar curvature of a coordinate metric."""

    dimension = len(coordinates)
    covariant = _square_matrix(metric, dimension)
    inverse = simplify_matrix(covariant.inv())
    ricci = ricci_tensor(coordinates, covariant)
    return sp.simplify(
        sum(
            inverse[i, j] * ricci[i, j]
            for i in range(dimension)
            for j in range(dimension)
        )
    )


def exterior_derivative_one_form(
    coordinates: Coordinates, one_form: Sequence[sp.Expr]
) -> sp.ImmutableMatrix:
    """Return the antisymmetric matrix ``(dA)_ij = d_i A_j - d_j A_i``."""

    dimension = len(coordinates)
    if len(one_form) != dimension:
        raise ValueError("one-form length must equal coordinate dimension")
    return sp.ImmutableMatrix(
        dimension,
        dimension,
        lambda i, j: sp.simplify(
            sp.diff(one_form[j], coordinates[i])
            - sp.diff(one_form[i], coordinates[j])
        ),
    )


def exterior_derivative_two_form(
    coordinates: Coordinates, two_form: sp.MatrixBase
) -> dict[tuple[int, int, int], sp.Expr]:
    """Return independent ordered components of ``dF``."""

    dimension = len(coordinates)
    form = sp.ImmutableMatrix(two_form)
    if form.shape != (dimension, dimension) or form != -form.T:
        raise ValueError("two-form must be an antisymmetric coordinate matrix")
    return {
        (i, j, k): sp.simplify(
            sp.diff(form[j, k], coordinates[i])
            + sp.diff(form[k, i], coordinates[j])
            + sp.diff(form[i, j], coordinates[k])
        )
        for i, j, k in combinations(range(dimension), 3)
    }


def kaluza_uplift_metric(
    base_metric: sp.MatrixBase,
    scalar: sp.Expr,
    potential: Sequence[sp.Expr],
) -> sp.ImmutableMatrix:
    """Build the convention-fixed five-dimensional Kaluza block metric.

    The ansatz is

    ``g_hat = exp(-phi/sqrt(3)) g + exp(2 phi/sqrt(3)) (dz + A)^2``.
    """

    dimension = len(potential)
    base = _square_matrix(base_metric, dimension)
    one_form = sp.ImmutableMatrix(dimension, 1, potential)
    base_warp = sp.exp(-scalar / sp.sqrt(3))
    fiber_warp = sp.exp(2 * scalar / sp.sqrt(3))

    uplift = sp.MutableDenseMatrix.zeros(dimension + 1, dimension + 1)
    uplift[:dimension, :dimension] = (
        base_warp * base + fiber_warp * one_form * one_form.T
    )
    uplift[:dimension, dimension] = fiber_warp * one_form
    uplift[dimension, :dimension] = (fiber_warp * one_form).T
    uplift[dimension, dimension] = fiber_warp
    return simplify_matrix(uplift)


@dataclass(frozen=True)
class EMDResiduals:
    """Convention-fixed Einstein--Maxwell--dilaton equation residuals."""

    einstein: sp.ImmutableMatrix
    maxwell: tuple[sp.Expr, ...]
    scalar: sp.Expr
    bianchi: dict[tuple[int, int, int], sp.Expr]

    def all_zero(self) -> bool:
        return (
            matrix_is_zero(self.einstein)
            and all(sp.simplify(value) == 0 for value in self.maxwell)
            and sp.simplify(self.scalar) == 0
            and all(sp.simplify(value) == 0 for value in self.bianchi.values())
        )


def emd_residuals(
    coordinates: Coordinates,
    metric: sp.MatrixBase,
    scalar: sp.Expr,
    potential: Sequence[sp.Expr],
    coupling: sp.Expr,
) -> EMDResiduals:
    """Compute the convention-fixed EMD field-equation residuals exactly.

    This follows ``docs/EMD_CONVENTION.md``:

    ``R_ij = 1/2 exp(a phi) (F_iρ F_j^ρ - 1/4 g_ij F²)
              + 1/2 (d_i phi)(d_j phi)``;
    ``nabla_i(exp(a phi) F^{ij}) = 0``;
    ``box(phi) - a/4 exp(a phi) F² = 0``.
    """

    dimension = len(coordinates)
    covariant = _square_matrix(metric, dimension)
    if len(potential) != dimension:
        raise ValueError("potential length must equal coordinate dimension")
    inverse = simplify_matrix(covariant.inv())
    gamma = christoffel_symbols(coordinates, covariant)
    ricci = ricci_tensor(coordinates, covariant)
    field = exterior_derivative_one_form(coordinates, potential)
    field_up = simplify_matrix(inverse * field * inverse)
    field_square = sp.simplify(
        sum(
            field[i, j] * field_up[i, j]
            for i in range(dimension)
            for j in range(dimension)
        )
    )
    scalar_gradient = tuple(sp.diff(scalar, coordinate) for coordinate in coordinates)
    weight = sp.exp(coupling * scalar)

    einstein = sp.MutableDenseMatrix.zeros(dimension, dimension)
    for i in range(dimension):
        for j in range(dimension):
            maxwell_product = sum(
                field[i, rho] * inverse[rho, sigma] * field[j, sigma]
                for rho in range(dimension)
                for sigma in range(dimension)
            )
            einstein[i, j] = sp.simplify(
                ricci[i, j]
                - sp.Rational(1, 2)
                * weight
                * (
                    maxwell_product
                    - sp.Rational(1, 4) * covariant[i, j] * field_square
                )
                - sp.Rational(1, 2) * scalar_gradient[i] * scalar_gradient[j]
            )

    weighted_field_up = simplify_matrix(weight * field_up)
    maxwell = []
    for j in range(dimension):
        component = sp.S.Zero
        for i in range(dimension):
            component += sp.diff(weighted_field_up[i, j], coordinates[i])
            for ell in range(dimension):
                component += gamma[i][i][ell] * weighted_field_up[ell, j]
                component += gamma[j][i][ell] * weighted_field_up[i, ell]
        maxwell.append(sp.simplify(component))

    wave = sp.S.Zero
    for i in range(dimension):
        for j in range(dimension):
            second_covariant = sp.diff(scalar_gradient[j], coordinates[i])
            second_covariant -= sum(
                gamma[ell][i][j] * scalar_gradient[ell]
                for ell in range(dimension)
            )
            wave += inverse[i, j] * second_covariant

    scalar_residual = sp.simplify(
        wave - sp.Rational(1, 4) * coupling * weight * field_square
    )
    return EMDResiduals(
        einstein=sp.ImmutableMatrix(einstein),
        maxwell=tuple(maxwell),
        scalar=scalar_residual,
        bianchi=exterior_derivative_two_form(coordinates, field),
    )
