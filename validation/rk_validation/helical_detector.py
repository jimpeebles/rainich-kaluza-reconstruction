"""Exact literal scalar-jet routing for the helical detector benchmark."""

from __future__ import annotations

import time

import sympy as sp

from rk_validation.exact import (
    exterior_derivative_one_form,
    hodge_star_two_form,
    ricci_tensor,
    simplify_matrix,
)


def _matrix_zero(matrix: sp.MatrixBase) -> bool:
    return all(sp.simplify(entry) == 0 for entry in matrix)


def _positive(expression: sp.Expr) -> bool:
    return sp.ask(sp.Q.positive(sp.simplify(expression))) is True


def _negative(expression: sp.Expr) -> bool:
    return sp.ask(sp.Q.negative(sp.simplify(expression))) is True


def _coordinate_hodge_two_form(
    metric: sp.MatrixBase, two_form: sp.MatrixBase
) -> sp.ImmutableMatrix:
    """Literal four-dimensional coordinate Hodge formula used by Lean."""
    inverse = simplify_matrix(metric.inv())
    raised = simplify_matrix(inverse * two_form * inverse.T)

    def epsilon(i: int, j: int, k: int, l: int) -> int:
        indices = tuple(map(int, (i, j, k, l)))
        if len(set(indices)) != 4:
            return 0
        inversions = sum(
            indices[a] > indices[b]
            for a in range(4)
            for b in range(a + 1, 4)
        )
        return -1 if inversions % 2 else 1

    complement = sp.ImmutableMatrix(
        4,
        4,
        lambda i, j: sum(
            epsilon(i, j, k, l) * raised[k, l]
            for k in range(4)
            for l in range(4)
        ),
    )
    return simplify_matrix(-sp.sqrt(-metric.det()) * complement / 2)


def replacement_upstream_point_certificate(
    metric: sp.ImmutableMatrix,
    mixed_ricci: sp.ImmutableMatrix,
    q_sq: sp.Expr,
    selected_scalar: sp.ImmutableMatrix,
) -> dict[str, object]:
    """Route the literal pointwise suffix after scalar closure.

    The selected scalar has already been certified equal to the literal
    fixed-probe candidate.  This routine evaluates the reconstruction and
    Maxwell gates, performs the finite Maxwell-frame search, and checks the
    selected coordinate Hodge equality exactly.
    """
    identity = sp.eye(4)
    raised_scalar = simplify_matrix(metric.inv() * selected_scalar)
    scalar_contribution = simplify_matrix(raised_scalar * selected_scalar.T / 2)
    scalar_trace = sp.simplify((selected_scalar.T * raised_scalar)[0] / 2)
    reconstruction = simplify_matrix(
        mixed_ricci * scalar_contribution
        + scalar_contribution * mixed_ricci
        - scalar_trace * scalar_contribution
        - (mixed_ricci * mixed_ricci - q_sq * identity)
    )

    residual = simplify_matrix(mixed_ricci - scalar_contribution)
    q = sp.sqrt(q_sq)
    minus_projector = simplify_matrix((identity - residual / q) / 2)
    plus_projector = simplify_matrix((identity + residual / q) / 2)
    maxwell_checks = {
        "square": _matrix_zero(residual * residual - q_sq * identity),
        "metric_self_adjoint": _matrix_zero(
            (metric * residual).T - metric * residual
        ),
        "minus_idempotent": _matrix_zero(
            minus_projector * minus_projector - minus_projector
        ),
        "plus_idempotent": _matrix_zero(
            plus_projector * plus_projector - plus_projector
        ),
        "mutually_annihilating": _matrix_zero(minus_projector * plus_projector),
        "complementary": _matrix_zero(minus_projector + plus_projector - identity),
    }

    def pairing(left: sp.MatrixBase, right: sp.MatrixBase) -> sp.Expr:
        return sp.simplify((left.T * metric * right)[0])

    def orthogonal_remainder(
        pivot: sp.MatrixBase, companion: sp.MatrixBase
    ) -> sp.ImmutableMatrix:
        return simplify_matrix(
            companion - pairing(pivot, companion) * pivot / pairing(pivot, pivot)
        )

    recipes = (
        "first",
        "second",
        "firstWeighted",
        "secondWeighted",
        "sum",
        "difference",
    )

    def pivot_pair(
        x: sp.MatrixBase, y: sp.MatrixBase, recipe: str
    ) -> tuple[sp.ImmutableMatrix, sp.ImmutableMatrix]:
        if recipe == "first":
            return sp.ImmutableMatrix(x), sp.ImmutableMatrix(y)
        if recipe == "second":
            return sp.ImmutableMatrix(y), sp.ImmutableMatrix(x)
        if recipe == "firstWeighted":
            return simplify_matrix(pairing(x, y) * x - pairing(x, x) * y), sp.ImmutableMatrix(x)
        if recipe == "secondWeighted":
            return simplify_matrix(pairing(y, y) * x - pairing(x, y) * y), sp.ImmutableMatrix(y)
        if recipe == "sum":
            return simplify_matrix(x + y), sp.ImmutableMatrix(x)
        return simplify_matrix(x - y), sp.ImmutableMatrix(x)

    minus_candidates: list[
        tuple[
            int,
            int,
            str,
            sp.ImmutableMatrix,
            sp.ImmutableMatrix,
            sp.Expr,
            sp.Expr,
        ]
    ] = []
    for probe0 in range(4):
        for probe1 in range(4):
            x = minus_projector[:, probe0]
            y = minus_projector[:, probe1]
            for recipe in recipes:
                pivot, companion = pivot_pair(x, y, recipe)
                pivot_norm = pairing(pivot, pivot)
                if not _negative(pivot_norm):
                    continue
                remainder = orthogonal_remainder(pivot, companion)
                remainder_norm = pairing(remainder, remainder)
                if _positive(remainder_norm):
                    minus_candidates.append(
                        (
                            probe0,
                            probe1,
                            recipe,
                            pivot,
                            remainder,
                            pivot_norm,
                            remainder_norm,
                        )
                    )

    plus_candidates: list[
        tuple[int, int, sp.ImmutableMatrix, sp.ImmutableMatrix, sp.Expr, sp.Expr]
    ] = []
    for probe0 in range(4):
        for probe1 in range(4):
            pivot = plus_projector[:, probe0]
            pivot_norm = pairing(pivot, pivot)
            if not _positive(pivot_norm):
                continue
            remainder = orthogonal_remainder(pivot, plus_projector[:, probe1])
            remainder_norm = pairing(remainder, remainder)
            if _positive(remainder_norm):
                plus_candidates.append(
                    (probe0, probe1, pivot, remainder, pivot_norm, remainder_norm)
                )

    if not minus_candidates or not plus_candidates:
        return {
            "reconstruction_zero": _matrix_zero(reconstruction),
            "reconstruction_obstruction": reconstruction,
            "maxwell_checks": maxwell_checks,
            "maxwell_entrance": all(maxwell_checks.values()),
            "frame_found": False,
            "minus_candidate_count": len(minus_candidates),
            "plus_candidate_count": len(plus_candidates),
        }

    (
        minus_probe0,
        minus_probe1,
        recipe,
        timelike,
        lorentz_remainder,
        timelike_norm,
        lorentz_remainder_norm,
    ) = minus_candidates[0]
    (
        plus_probe0,
        plus_probe1,
        spacelike,
        space_remainder,
        spacelike_norm,
        space_remainder_norm,
    ) = plus_candidates[0]
    tetrad = simplify_matrix(
        sp.Matrix.hstack(
            timelike / sp.sqrt(-timelike_norm),
            lorentz_remainder / sp.sqrt(lorentz_remainder_norm),
            spacelike / sp.sqrt(spacelike_norm),
            space_remainder / sp.sqrt(space_remainder_norm),
        )
    )
    minkowski = sp.diag(-1, 1, 1, 1)
    frame_det = sp.simplify(sp.radsimp(tetrad.det()))
    base_coframe = simplify_matrix(tetrad.inv())
    if _positive(frame_det):
        orientation_reverse = False
        coframe = base_coframe
    elif _negative(frame_det):
        orientation_reverse = True
        coframe = simplify_matrix(sp.diag(1, 1, 1, -1) * base_coframe)
    else:
        raise AssertionError("selected exact frame determinant has unknown sign")
    coframe_det = sp.simplify((-1 if orientation_reverse else 1) / frame_det)
    amplitude = sp.sqrt(2 * q)
    canonical_electric = sp.zeros(4)
    canonical_electric[0, 1] = amplitude
    canonical_electric[1, 0] = -amplitude
    canonical_hodge = sp.zeros(4)
    canonical_hodge[2, 3] = amplitude
    canonical_hodge[3, 2] = -amplitude
    electric_seed = simplify_matrix(coframe.T * canonical_electric * coframe)
    transported_hodge = simplify_matrix(coframe.T * canonical_hodge * coframe)
    metric_hodge = _coordinate_hodge_two_form(metric, electric_seed)
    frame_signs = (
        timelike_norm,
        lorentz_remainder_norm,
        spacelike_norm,
        space_remainder_norm,
    )
    return {
        "reconstruction_zero": _matrix_zero(reconstruction),
        "reconstruction_obstruction": reconstruction,
        "maxwell_checks": maxwell_checks,
        "maxwell_entrance": all(maxwell_checks.values()),
        "residual": residual,
        "minus_projector": minus_projector,
        "plus_projector": plus_projector,
        "frame_found": True,
        "minus_candidate_count": len(minus_candidates),
        "plus_candidate_count": len(plus_candidates),
        "frame_choice": {
            "maxwellMinusProbe0": minus_probe0,
            "maxwellMinusProbe1": minus_probe1,
            "maxwellMinusPivotRecipe": recipe,
            "maxwellPlusProbe0": plus_probe0,
            "maxwellPlusProbe1": plus_probe1,
            "orientationReverse": orientation_reverse,
        },
        "frame_signs": frame_signs,
        "pseudo_orthonormal": _matrix_zero(tetrad.T * metric * tetrad - minkowski),
        "frame_det": frame_det,
        "coframe_metric": _matrix_zero(coframe.T * minkowski * coframe - metric),
        "coframe_det": coframe_det,
        "coframe_det_positive": _positive(coframe_det),
        "hodge_obstruction": simplify_matrix(metric_hodge - transported_hodge),
        "hodge_compatible": _matrix_zero(metric_hodge - transported_hodge),
    }


def replacement_physical_active_certificate(
    coordinates: tuple[sp.Symbol, ...],
    metric: sp.ImmutableMatrix,
    scalar: sp.Expr,
    potential: tuple[sp.Expr, ...],
    fiber_norm: sp.Expr,
    mixed_ricci_at_point: sp.ImmutableMatrix,
    q_sq_at_point: sp.Expr,
) -> dict[str, object]:
    """Exact choice-free physical active-wedge certificate.

    The local volume density uses the positive ``r>0, sin(theta)>0`` germ
    containing the replacement point.  ``hodge_star_two_form`` has the
    opposite orientation sign from Lean's ``coordinateMetricHodgeTwoForm4``,
    hence the explicit negation below.
    """
    t, radius, theta, phi = coordinates
    point = {
        t: sp.S.Zero,
        radius: sp.Rational(3, 2),
        theta: sp.pi / 4,
        phi: sp.S.Zero,
    }
    inverse = simplify_matrix(metric.inv())
    physical_field = simplify_matrix(
        fiber_norm ** sp.Rational(3, 4)
        * exterior_derivative_one_form(coordinates, potential)
        / sp.sqrt(2)
    )
    local_density = sp.sqrt(
        radius**3 * (radius**3 * sp.sin(theta) ** 2 + radius + 2)
    ) * sp.sin(theta)
    physical_hodge = simplify_matrix(
        -hodge_star_two_form(metric, physical_field, volume_density=local_density)
    )
    core_ff = simplify_matrix(inverse * physical_field * inverse * physical_field)
    core_fh = simplify_matrix(inverse * physical_field * inverse * physical_hodge)
    trace_ff = sp.factor(sp.trace(core_ff))
    trace_fh = sp.factor(sp.trace(core_fh))
    physical_q = sp.factor(sp.sqrt(sp.factor(trace_ff**2 + trace_fh**2)) / 4)
    cosine = sp.factor(trace_ff / (4 * physical_q))
    sine = sp.factor(-trace_fh / (4 * physical_q))
    unit_circle = sp.factor(cosine**2 + sine**2)
    omega = sp.ImmutableMatrix(
        [
            sp.factor(
                (
                    cosine * sp.diff(sine, coordinate)
                    - sine * sp.diff(cosine, coordinate)
                )
                / 2
            )
            for coordinate in coordinates
        ]
    )

    metric_point = simplify_matrix(metric.subs(point))
    inverse_point = simplify_matrix(metric_point.inv())
    field_point = simplify_matrix(physical_field.subs(point))
    hodge_point = simplify_matrix(physical_hodge.subs(point))
    literal_hodge_point = _coordinate_hodge_two_form(metric_point, field_point)
    hodge_squared_point = _coordinate_hodge_two_form(metric_point, literal_hodge_point)
    density_point = sp.simplify(local_density.subs(point))
    omega_point = simplify_matrix(omega.subs(point))
    scalar_point = sp.ImmutableMatrix(
        [sp.simplify(sp.diff(scalar, coordinate).subs(point)) for coordinate in coordinates]
    )
    core_point = simplify_matrix(core_ff.subs(point))
    stress_point = simplify_matrix(
        -core_point + sp.trace(core_point) * sp.eye(4) / 4
    )
    raised_scalar = simplify_matrix(inverse_point * scalar_point)
    detector_residual = simplify_matrix(
        mixed_ricci_at_point - raised_scalar * scalar_point.T / 2
    )
    stress_scalar_action = simplify_matrix(stress_point.T * scalar_point)
    wedge = {
        (i, j): sp.simplify(
            omega_point[i] * stress_scalar_action[j]
            - omega_point[j] * stress_scalar_action[i]
        )
        for i in range(4)
        for j in range(i + 1, 4)
    }
    physical_q_point = sp.simplify(physical_q.subs(point))
    return {
        "local_density_squared": sp.simplify(local_density**2 + metric.det()),
        "local_density_at_point": density_point,
        "local_density_positive": _positive(density_point),
        "hodge_matches_literal_at_point": _matrix_zero(
            hodge_point - literal_hodge_point
        ),
        "hodge_squares_to_minus_at_point": _matrix_zero(
            hodge_squared_point + field_point
        ),
        "double_angle_unit_circle": sp.simplify(unit_circle - 1),
        "physical_q_at_point": physical_q_point,
        "detector_q_at_point": sp.sqrt(q_sq_at_point),
        "physical_q_matches_detector": sp.simplify(
            physical_q_point - sp.sqrt(q_sq_at_point)
        )
        == 0,
        "stress_matches_detector_residual": _matrix_zero(
            stress_point - detector_residual
        ),
        "stress_square_matches_detector_q_sq": _matrix_zero(
            stress_point * stress_point - q_sq_at_point * sp.eye(4)
        ),
        "omega_at_point": omega_point,
        "stress_scalar_action_at_point": stress_scalar_action,
        "wedge_components": wedge,
        "active_component": (1, 2),
        "active_value": wedge[(1, 2)],
        "active": sp.simplify(wedge[(1, 2)]) != 0,
    }


def _zero_certificate(expression: sp.Expr) -> tuple[bool, str, int, str]:
    expression = sp.together(expression)
    numerator = expression.as_numer_denom()[0]
    reduced_expression = sp.radsimp(expression)
    reduced = sp.simplify(reduced_expression)
    return reduced == 0, str(reduced), sp.count_ops(numerator), sp.sstr(expression)


def replacement_scalar_closure_certificate(
    coordinates: tuple[sp.Symbol, ...],
    metric: sp.ImmutableMatrix,
    scalar: sp.Expr,
) -> dict[str, object]:
    started = time.time()
    t, radius, theta, phi = coordinates
    point = {
        t: sp.S.Zero,
        radius: sp.Rational(3, 2),
        theta: sp.pi / 4,
        phi: sp.S.Zero,
    }
    ricci = ricci_tensor(coordinates, metric)
    mixed_field = simplify_matrix(metric.inv() * ricci)
    complementary = (1, 2)
    block_support = all(
        sp.simplify(field[i, j]) == 0
        for field in (metric, mixed_field)
        for i in range(4)
        for j in range(4)
        if (i in complementary) != (j in complementary)
    ) and all(
        coordinate not in expression.free_symbols
        for coordinate in (t, phi)
        for field in (metric, mixed_field)
        for expression in field
    )
    G = simplify_matrix(metric.subs(point))
    R = simplify_matrix(mixed_field.subs(point))
    G2 = G.extract((1, 2), (1, 2))
    R2 = R.extract((1, 2), (1, 2))
    dG2 = [
        simplify_matrix(metric.diff(coordinate).subs(point)).extract((1, 2), (1, 2))
        for coordinate in coordinates
    ]
    dR2 = [
        simplify_matrix(mixed_field.diff(coordinate).subs(point)).extract((1, 2), (1, 2))
        for coordinate in coordinates
    ]

    p1 = sp.trace(R)
    p2 = sp.trace(R * R)
    p3 = sp.trace(R * R * R)
    e1 = p1
    e2 = sp.simplify((p1**2 - p2) / 2)
    e3 = sp.simplify((p1**3 - 3 * p1 * p2 + 2 * p3) / 6)
    q_sq = sp.simplify(-e3 / e1)
    residual_constant = sp.simplify(-e2 - q_sq)
    discriminant = sp.simplify(e1**2 + 4 * residual_constant)
    q = sp.sqrt(q_sq)
    root_a = sp.simplify((e1 - sp.sqrt(discriminant)) / 2)
    root_b = sp.simplify((e1 + sp.sqrt(discriminant)) / 2)

    root_jets: list[tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]] = []
    for dR_full in [simplify_matrix(mixed_field.diff(x).subs(point)) for x in coordinates]:
        de1 = sp.trace(dR_full)
        dp2 = 2 * sp.trace(R * dR_full)
        dp3 = 3 * sp.trace(R * R * dR_full)
        de2 = sp.simplify(e1 * de1 - dp2 / 2)
        de3 = sp.simplify(
            (3 * e1**2 * de1 - 3 * (de1 * p2 + e1 * dp2) + 2 * dp3) / 6
        )
        dq_sq = sp.simplify(-(de3 * e1 - e3 * de1) / e1**2)
        dresidual = sp.simplify(-de2 - dq_sq)
        ddiscriminant = sp.simplify(2 * e1 * de1 + 4 * dresidual)
        dq = sp.simplify(dq_sq / (2 * q))
        da = sp.simplify((de1 - ddiscriminant / (2 * sp.sqrt(discriminant))) / 2)
        db = sp.simplify((de1 + ddiscriminant / (2 * sp.sqrt(discriminant))) / 2)
        root_jets.append((da, db, dq, dq_sq))

    identity = sp.eye(2)

    def projector_and_jet(
        target: sp.Expr,
        others: tuple[sp.Expr, sp.Expr, sp.Expr],
        dtarget: sp.Expr,
        dothers: tuple[sp.Expr, sp.Expr, sp.Expr],
        dR: sp.MatrixBase,
    ) -> tuple[sp.ImmutableMatrix, sp.ImmutableMatrix]:
        factors = tuple(R2 - other * identity for other in others)
        numerator = factors[0] * factors[1] * factors[2]
        denominator = sp.prod(target - other for other in others)
        derivatives = tuple(
            dR - dother * identity for dother in dothers
        )
        dnumerator = (
            derivatives[0] * factors[1] * factors[2]
            + factors[0] * derivatives[1] * factors[2]
            + factors[0] * factors[1] * derivatives[2]
        )
        ddenominator = sum(
            (dtarget - dothers[index])
            * sp.prod(
                target - others[other_index]
                for other_index in range(3)
                if other_index != index
            )
            for index in range(3)
        )
        return (
            simplify_matrix(numerator / denominator),
            simplify_matrix(
                dnumerator / denominator
                - numerator * ddenominator / denominator**2
            ),
        )

    PA_jets: list[sp.ImmutableMatrix] = []
    PB_jets: list[sp.ImmutableMatrix] = []
    PA = PB = None
    for direction, (da, db, dq, _) in enumerate(root_jets):
        PA, dPA = projector_and_jet(
            root_a, (-q, root_b, q), da, (-dq, db, dq), dR2[direction]
        )
        PB, dPB = projector_and_jet(
            root_b, (root_a, -q, q), db, (da, -dq, dq), dR2[direction]
        )
        PA_jets.append(dPA)
        PB_jets.append(dPB)
    assert PA is not None and PB is not None

    diagonal_a = sp.simplify((root_a**2 - q_sq) / (root_a - root_b))
    diagonal_b = sp.simplify((root_b**2 - q_sq) / (root_b - root_a))

    def diagonal_jet(
        which: str, da: sp.Expr, db: sp.Expr, dq_sq: sp.Expr
    ) -> sp.Expr:
        if which == "a":
            return sp.simplify(
                ((2 * root_a * da - dq_sq) * (root_a - root_b)
                 - (root_a**2 - q_sq) * (da - db))
                / (root_a - root_b) ** 2
            )
        return sp.simplify(
            ((2 * root_b * db - dq_sq) * (root_b - root_a)
             - (root_b**2 - q_sq) * (db - da))
            / (root_b - root_a) ** 2
        )

    def component_and_jet(
        P: sp.MatrixBase,
        dP: sp.MatrixBase,
        probe: int,
        Gjet: sp.MatrixBase,
        diagonal: sp.Expr,
        ddiagonal: sp.Expr,
        timelike: bool,
    ) -> tuple[sp.ImmutableMatrix, sp.ImmutableMatrix]:
        x = P[:, probe]
        dx = dP[:, probe]
        norm = sp.simplify((x.T * G2 * x)[0])
        dnorm = sp.simplify(
            (dx.T * G2 * x)[0]
            + (x.T * Gjet * x)[0]
            + (x.T * G2 * dx)[0]
        )
        sign = -1 if timelike else 1
        amplitude = sp.sqrt(2 * sign * diagonal)
        damplitude = sp.simplify(sign * ddiagonal / amplitude)
        scale = sp.sqrt(sign * norm)
        dscale = sp.simplify(sign * dnorm / (2 * scale))
        theta_value = G2 * x / scale
        dtheta = (Gjet * x + G2 * dx) / scale - G2 * x * dscale / scale**2
        value = amplitude * theta_value
        derivative = damplitude * theta_value + amplitude * dtheta
        return sp.ImmutableMatrix(value), sp.ImmutableMatrix(derivative)

    selected_value = None
    selected_jets: list[sp.ImmutableMatrix] = []
    for direction, (da, db, _, dq_sq) in enumerate(root_jets):
        du = diagonal_jet("a", da, db, dq_sq)
        dv = diagonal_jet("b", da, db, dq_sq)
        alpha, dalpha = component_and_jet(
            PA, PA_jets[direction], 0, dG2[direction], diagonal_a, du, True
        )
        beta, dbeta = component_and_jet(
            PB, PB_jets[direction], 1, dG2[direction], diagonal_b, dv, False
        )
        selected_value = alpha + beta
        selected_jets.append(dalpha + dbeta)
    assert selected_value is not None

    closure = selected_jets[1][1] - selected_jets[2][0]
    certified, reduced, operations, raw_expression = _zero_certificate(closure)
    physical_hessian_difference = sp.diff(scalar, radius, theta).subs(point) - sp.diff(
        scalar, theta, radius
    ).subs(point)
    return {
        "certified_zero": certified,
        "full_closure_from_block_support": certified and block_support,
        "block_support": block_support,
        "reduced_expression": reduced,
        "raw_expression": raw_expression,
        "raw_numerator_operations": operations,
        "physical_hessian_antisymmetry": str(sp.simplify(physical_hessian_difference)),
        "elapsed_seconds": round(time.time() - started, 3),
    }
