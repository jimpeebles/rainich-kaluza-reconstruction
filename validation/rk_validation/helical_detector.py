"""Exact literal scalar-jet routing for the helical detector benchmark."""

from __future__ import annotations

import time

import sympy as sp

from rk_validation.exact import ricci_tensor, simplify_matrix


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
