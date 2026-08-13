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


def _metric_two_jet_at(
    coordinates: Coordinates,
    metric: sp.MatrixBase,
    substitutions: dict[sp.Symbol, sp.Expr],
) -> tuple[
    sp.ImmutableMatrix,
    sp.ImmutableMatrix,
    tuple[sp.ImmutableMatrix, ...],
    tuple[tuple[sp.ImmutableMatrix, ...], ...],
    tuple[tuple[tuple[sp.Expr, ...], ...], ...],
    tuple[tuple[tuple[tuple[sp.Expr, ...], ...], ...], ...],
]:
    """Evaluate a metric two-jet, its inverse, and connection jet exactly."""

    dimension = len(coordinates)
    covariant = _square_matrix(metric, dimension)

    def at(expression: sp.Expr) -> sp.Expr:
        return sp.simplify(expression.subs(substitutions))

    point_metric = sp.ImmutableMatrix(covariant.applyfunc(at))
    inverse = simplify_matrix(point_metric.inv())
    first = tuple(
        sp.ImmutableMatrix(
            dimension,
            dimension,
            lambda i, j: at(sp.diff(covariant[i, j], coordinate)),
        )
        for coordinate in coordinates
    )
    second = tuple(
        tuple(
            sp.ImmutableMatrix(
                dimension,
                dimension,
                lambda i, j: at(
                    sp.diff(covariant[i, j], coordinate, second_coordinate)
                ),
            )
            for second_coordinate in coordinates
        )
        for coordinate in coordinates
    )
    inverse_first = tuple(
        simplify_matrix(-inverse * derivative * inverse) for derivative in first
    )

    gamma = tuple(
        tuple(
            tuple(
                sp.simplify(
                    sp.Rational(1, 2)
                    * sum(
                        inverse[k, ell]
                        * (
                            first[i][ell, j]
                            + first[j][ell, i]
                            - first[ell][i, j]
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
    gamma_first = tuple(
        tuple(
            tuple(
                tuple(
                    sp.simplify(
                        sp.Rational(1, 2)
                        * sum(
                            inverse_first[derivative][k, ell]
                            * (
                                first[i][ell, j]
                                + first[j][ell, i]
                                - first[ell][i, j]
                            )
                            + inverse[k, ell]
                            * (
                                second[derivative][i][ell, j]
                                + second[derivative][j][ell, i]
                                - second[derivative][ell][i, j]
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
        for derivative in range(dimension)
    )
    return point_metric, inverse, first, second, gamma, gamma_first


def ricci_tensor_at(
    coordinates: Coordinates,
    metric: sp.MatrixBase,
    substitutions: dict[sp.Symbol, sp.Expr],
) -> sp.ImmutableMatrix:
    """Compute exact Ricci components at a point from the metric two-jet.

    This avoids globally simplifying a large symbolic Ricci tensor before a
    benchmark substitutes its exact generic point.
    """

    dimension = len(coordinates)
    _, _, _, _, gamma, gamma_first = _metric_two_jet_at(
        coordinates, metric, substitutions
    )
    result = sp.MutableDenseMatrix.zeros(dimension, dimension)
    for i in range(dimension):
        for j in range(dimension):
            component = sp.S.Zero
            for k in range(dimension):
                component += gamma_first[k][k][i][j]
                component -= gamma_first[j][k][i][k]
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
    if form.shape != (dimension, dimension) or not matrix_is_zero(form + form.T):
        raise ValueError("two-form must be an antisymmetric coordinate matrix")
    return {
        (i, j, k): sp.simplify(
            sp.diff(form[j, k], coordinates[i])
            + sp.diff(form[k, i], coordinates[j])
            + sp.diff(form[i, j], coordinates[k])
        )
        for i, j, k in combinations(range(dimension), 3)
    }


def wedge_one_form_two_form(
    one_form: Sequence[sp.Expr], two_form: sp.MatrixBase
) -> dict[tuple[int, int, int], sp.Expr]:
    """Return independent components of the three-form ``one_form ∧ two_form``."""

    dimension = len(one_form)
    form = sp.ImmutableMatrix(two_form)
    if form.shape != (dimension, dimension) or not matrix_is_zero(form + form.T):
        raise ValueError("two-form must be an antisymmetric coordinate matrix")
    return {
        (i, j, k): sp.simplify(
            one_form[i] * form[j, k]
            + one_form[j] * form[k, i]
            + one_form[k] * form[i, j]
        )
        for i, j, k in combinations(range(dimension), 3)
    }


def hodge_star_two_form(
    metric: sp.MatrixBase,
    two_form: sp.MatrixBase,
    *,
    volume_density: sp.Expr | None = None,
) -> sp.ImmutableMatrix:
    """Return the covariant Hodge dual of a two-form in four dimensions.

    ``volume_density`` may be supplied when the coordinate patch fixes the
    sign of a trigonometric or radical factor that ``sqrt(Abs(det(g)))`` cannot
    simplify symbolically.  Orientation is ``epsilon[0,1,2,3] = +1``.
    """

    dimension = 4
    covariant = _square_matrix(metric, dimension)
    form = sp.ImmutableMatrix(two_form)
    if form.shape != (dimension, dimension) or not matrix_is_zero(form + form.T):
        raise ValueError("two-form must be a four-dimensional antisymmetric matrix")
    inverse = simplify_matrix(covariant.inv())
    raised = simplify_matrix(inverse * form * inverse)
    density = (
        sp.sqrt(sp.Abs(sp.simplify(covariant.det())))
        if volume_density is None
        else sp.sympify(volume_density)
    )
    return sp.ImmutableMatrix(
        dimension,
        dimension,
        lambda i, j: sp.simplify(
            sp.Rational(1, 2)
            * density
            * sum(
                sp.LeviCivita(i, j, k, ell) * raised[k, ell]
                for k in range(dimension)
                for ell in range(dimension)
            )
        ),
    )


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


def principal_reflection_covector(
    one_form: Sequence[sp.Expr],
) -> tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]:
    """Apply the canonical Maxwell-plane reflection ``diag(-1,-1,1,1)``."""

    if len(one_form) != 4:
        raise ValueError("principal reflection requires a four-dimensional one-form")
    return tuple(
        sp.simplify(sign * component)
        for sign, component in zip((-1, -1, 1, 1), one_form, strict=True)
    )


def effective_complexion_one_form(
    omega: Sequence[sp.Expr],
    scalar_covector: Sequence[sp.Expr],
    sine_coupling: sp.Expr,
) -> tuple[sp.Expr, ...]:
    """Return ``eta = omega + (B/2) Jv`` in the canonical principal frame."""

    if len(omega) != 4 or len(scalar_covector) != 4:
        raise ValueError("effective complexion data must be four-dimensional")
    reflected = principal_reflection_covector(scalar_covector)
    return tuple(
        sp.simplify(component + sine_coupling * image / 2)
        for component, image in zip(omega, reflected, strict=True)
    )


def one_form_wedge_component(
    left: Sequence[sp.Expr],
    right: Sequence[sp.Expr],
    i: int,
    j: int,
) -> sp.Expr:
    """Return the ordered ``(i,j)`` component of ``left ∧ right``."""

    if len(left) != 4 or len(right) != 4:
        raise ValueError("wedge quotient data must be four-dimensional")
    if not 0 <= i < 4 or not 0 <= j < 4:
        raise IndexError("wedge quotient indices must lie in range(4)")
    return sp.simplify(left[i] * right[j] - left[j] * right[i])


def next_order_sine_coupling_candidate(
    cosine_derivative: Sequence[sp.Expr],
    effective_complexion: Sequence[sp.Expr],
    scalar_covector: Sequence[sp.Expr],
    i: int,
    j: int,
) -> sp.Expr:
    """Recover ``B`` from one nonzero component of the fourth-order quotient."""

    if len(cosine_derivative) != 4:
        raise ValueError("cosine derivative must be four-dimensional")
    reflected = principal_reflection_covector(scalar_covector)
    denominator = 2 * one_form_wedge_component(
        effective_complexion, reflected, i, j
    )
    if sp.simplify(denominator) == 0:
        raise ZeroDivisionError("selected eta-wedge-Jv component vanishes")
    numerator = -one_form_wedge_component(
        cosine_derivative, reflected, i, j
    )
    return sp.simplify(numerator / denominator)


def next_order_sine_residual(
    cosine_derivative: Sequence[sp.Expr],
    effective_complexion: Sequence[sp.Expr],
    scalar_covector: Sequence[sp.Expr],
    sine_coupling: sp.Expr,
) -> tuple[sp.Expr, ...]:
    """Return ``dA + 2 B eta - B^2 Jv`` componentwise."""

    if len(cosine_derivative) != 4 or len(effective_complexion) != 4:
        raise ValueError("next-order data must be four-dimensional")
    reflected = principal_reflection_covector(scalar_covector)
    return tuple(
        sp.simplify(dA + 2 * sine_coupling * eta - sine_coupling**2 * Jv)
        for dA, eta, Jv in zip(
            cosine_derivative, effective_complexion, reflected, strict=True
        )
    )


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


def emd_residuals_at(
    coordinates: Coordinates,
    metric: sp.MatrixBase,
    scalar: sp.Expr,
    potential: Sequence[sp.Expr],
    coupling: sp.Expr,
    substitutions: dict[sp.Symbol, sp.Expr],
) -> EMDResiduals:
    """Evaluate the convention-fixed EMD residuals from exact field jets."""

    dimension = len(coordinates)
    if len(potential) != dimension:
        raise ValueError("potential length must equal coordinate dimension")
    covariant = _square_matrix(metric, dimension)
    point_metric, inverse, metric_first, _, gamma, gamma_first = _metric_two_jet_at(
        coordinates, covariant, substitutions
    )

    def at(expression: sp.Expr) -> sp.Expr:
        return sp.simplify(expression.subs(substitutions))

    ricci = sp.MutableDenseMatrix.zeros(dimension, dimension)
    for i in range(dimension):
        for j in range(dimension):
            component = sp.S.Zero
            for k in range(dimension):
                component += gamma_first[k][k][i][j]
                component -= gamma_first[j][k][i][k]
                for ell in range(dimension):
                    component += gamma[k][i][j] * gamma[ell][k][ell]
                    component -= gamma[ell][i][k] * gamma[k][j][ell]
            ricci[i, j] = sp.simplify(component)

    field_symbolic = exterior_derivative_one_form(coordinates, potential)
    field = sp.ImmutableMatrix(field_symbolic.applyfunc(at))
    field_first = tuple(
        sp.ImmutableMatrix(
            dimension,
            dimension,
            lambda i, j: at(sp.diff(field_symbolic[i, j], coordinate)),
        )
        for coordinate in coordinates
    )
    inverse_first = tuple(
        simplify_matrix(-inverse * derivative * inverse)
        for derivative in metric_first
    )
    field_up = simplify_matrix(inverse * field * inverse)
    field_up_first = tuple(
        simplify_matrix(
            inverse_first[k] * field * inverse
            + inverse * field_first[k] * inverse
            + inverse * field * inverse_first[k]
        )
        for k in range(dimension)
    )
    field_square = sp.simplify(
        sum(
            field[i, j] * field_up[i, j]
            for i in range(dimension)
            for j in range(dimension)
        )
    )
    scalar_gradient = tuple(
        at(sp.diff(scalar, coordinate)) for coordinate in coordinates
    )
    scalar_hessian = tuple(
        tuple(
            at(sp.diff(scalar, coordinates[i], coordinates[j]))
            for j in range(dimension)
        )
        for i in range(dimension)
    )
    point_weight = at(sp.exp(coupling * scalar))

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
                * point_weight
                * (
                    maxwell_product
                    - sp.Rational(1, 4) * point_metric[i, j] * field_square
                )
                - sp.Rational(1, 2) * scalar_gradient[i] * scalar_gradient[j]
            )

    weighted_field_up = simplify_matrix(point_weight * field_up)
    weighted_field_up_first = tuple(
        simplify_matrix(
            point_weight
            * (
                coupling * scalar_gradient[k] * field_up
                + field_up_first[k]
            )
        )
        for k in range(dimension)
    )
    maxwell = []
    for j in range(dimension):
        component = sp.S.Zero
        for i in range(dimension):
            component += weighted_field_up_first[i][i, j]
            for ell in range(dimension):
                component += gamma[i][i][ell] * weighted_field_up[ell, j]
                component += gamma[j][i][ell] * weighted_field_up[i, ell]
        maxwell.append(sp.simplify(component))

    wave = sp.S.Zero
    for i in range(dimension):
        for j in range(dimension):
            second_covariant = scalar_hessian[i][j] - sum(
                gamma[ell][i][j] * scalar_gradient[ell]
                for ell in range(dimension)
            )
            wave += inverse[i, j] * second_covariant
    scalar_residual = sp.simplify(
        wave - sp.Rational(1, 4) * coupling * point_weight * field_square
    )
    bianchi = {
        index: at(value)
        for index, value in exterior_derivative_two_form(
            coordinates, field_symbolic
        ).items()
    }
    return EMDResiduals(
        einstein=sp.ImmutableMatrix(einstein),
        maxwell=tuple(maxwell),
        scalar=scalar_residual,
        bianchi=bianchi,
    )
