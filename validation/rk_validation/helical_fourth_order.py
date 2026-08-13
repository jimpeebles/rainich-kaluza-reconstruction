"""Exact finite fourth-order algebra for the selected helical branch.

The selected frame introduces three nested square roots beyond the four
quadratic radicals already present at the replacement point.  SymPy's
generic simplifier is not a reliable zero oracle in that algebra, so this
module evaluates the final channel in an explicit 128-slot square-free
quadratic quotient representation.  The reduction rules certify zero
identities.  They do not, by themselves, prove that all 128 slots are
linearly independent over the rationals.

The certificate deliberately distinguishes the literal point/frame/channel
calculation from the last derivative.  ``physical_dA`` is the derivative
supplied by the exact constant-coupling EMD solution.  Identifying it with
the derivative of the detector's literal quotient *field* still requires a
neighborhood (or second-jet) bridge and is not asserted here.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
import hashlib
from itertools import product
import json

import sympy as sp

from rk_validation.exact import exterior_derivative_one_form, simplify_matrix


def _simplify_matrix(matrix: sp.MatrixBase) -> sp.ImmutableMatrix:
    return sp.ImmutableMatrix(matrix.applyfunc(sp.simplify))


class _Tower:
    """Element of the seven-generator quadratic tower used by this point."""

    base_squares = (
        Fraction(2),
        Fraction(3),
        Fraction(83),
        Fraction(17953),
    )
    extension_relations: tuple[dict[int, Fraction], ...] = ()

    def __init__(self, coefficients: dict[int, Fraction] | None = None):
        self.coefficients = {
            mask: Fraction(value)
            for mask, value in (coefficients or {}).items()
            if value
        }

    @classmethod
    def rational(cls, value: object) -> _Tower:
        rational = sp.Rational(value)
        return cls({0: Fraction(int(rational.p), int(rational.q))})

    @classmethod
    def generator(cls, index: int) -> _Tower:
        return cls({1 << index: Fraction(1)})

    @staticmethod
    @lru_cache(None)
    def _multiply_masks(left: int, right: int) -> dict[int, Fraction]:
        common = left & right
        remaining = left ^ right
        factor: dict[int, Fraction] = {0: Fraction(1)}
        for bit, square in enumerate(_Tower.base_squares):
            if common & (1 << bit):
                factor = {mask: value * square for mask, value in factor.items()}
        for bit in range(4, 7):
            if not common & (1 << bit):
                continue
            expanded: dict[int, Fraction] = {}
            for first_mask, first_value in factor.items():
                for second_mask, second_value in _Tower.extension_relations[
                    bit - 4
                ].items():
                    overlap = first_mask & second_mask
                    mask = first_mask ^ second_mask
                    value = first_value * second_value
                    for base_bit, square in enumerate(_Tower.base_squares):
                        if overlap & (1 << base_bit):
                            value *= square
                    expanded[mask] = expanded.get(mask, Fraction()) + value
            factor = {mask: value for mask, value in expanded.items() if value}
        result: dict[int, Fraction] = {}
        base_remaining = remaining & 15
        extension_remaining = remaining & ~15
        for mask, coefficient in factor.items():
            overlap = base_remaining & mask
            value = coefficient
            for bit, square in enumerate(_Tower.base_squares):
                if overlap & (1 << bit):
                    value *= square
            key = extension_remaining | (base_remaining ^ mask)
            result[key] = result.get(key, Fraction()) + value
        return {mask: value for mask, value in result.items() if value}

    def __add__(self, other: object) -> _Tower:
        value = other if isinstance(other, _Tower) else _Tower.rational(other)
        result = dict(self.coefficients)
        for mask, coefficient in value.coefficients.items():
            result[mask] = result.get(mask, Fraction()) + coefficient
            if not result[mask]:
                del result[mask]
        return _Tower(result)

    __radd__ = __add__

    def __neg__(self) -> _Tower:
        return _Tower(
            {mask: -coefficient for mask, coefficient in self.coefficients.items()}
        )

    def __sub__(self, other: object) -> _Tower:
        return self + (-other)

    def __rsub__(self, other: object) -> _Tower:
        return _Tower.rational(other) - self

    def __mul__(self, other: object) -> _Tower:
        value = other if isinstance(other, _Tower) else _Tower.rational(other)
        result: dict[int, Fraction] = {}
        for left_mask, left_coefficient in self.coefficients.items():
            for right_mask, right_coefficient in value.coefficients.items():
                for mask, reduction in self._multiply_masks(
                    left_mask, right_mask
                ).items():
                    result[mask] = result.get(mask, Fraction()) + (
                        left_coefficient * right_coefficient * reduction
                    )
        return _Tower({mask: coefficient for mask, coefficient in result.items() if coefficient})

    __rmul__ = __mul__

    @property
    def is_zero(self) -> bool:
        return not self.coefficients


def _tower_element_payload(value: _Tower) -> list[list[int]]:
    """Canonical rational coefficient payload for one quotient element."""

    return [
        [mask, coefficient.numerator, coefficient.denominator]
        for mask, coefficient in sorted(value.coefficients.items())
    ]


def _tower_payload_sha256(values) -> str:
    """Bind an artifact to the actual quotient-algebra coefficient payload."""

    payload = [_tower_element_payload(value) for value in values]
    rendered = json.dumps(payload, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(rendered.encode("utf-8")).hexdigest()


def _tower_relations_sha256() -> str:
    """Bind all four base and three extension square relations."""

    payload = {
        "base_squares": [
            [index, square.numerator, square.denominator]
            for index, square in enumerate(_Tower.base_squares)
        ],
        "extension_squares": [
            [
                [mask, coefficient.numerator, coefficient.denominator]
                for mask, coefficient in sorted(relation.items())
            ]
            for relation in _Tower.extension_relations
        ],
    }
    rendered = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(rendered.encode("utf-8")).hexdigest()


def _tower_square_is_positive_rational(value: _Tower) -> bool:
    """Certify nonzero without assuming independence of all 128 slots."""

    square = value * value
    return (
        set(square.coefficients) == {0}
        and square.coefficients[0] > 0
    )


def _embed(expression: sp.Expr) -> _Tower:
    expression = sp.radsimp(sp.simplify(expression))
    symbols = sp.symbols("a b c d")
    replacements = {
        sp.sqrt(2): symbols[0],
        sp.sqrt(3): symbols[1],
        sp.sqrt(83): symbols[2],
        sp.sqrt(17953): symbols[3],
        sp.sqrt(498): symbols[0] * symbols[1] * symbols[2],
        sp.sqrt(53859): symbols[1] * symbols[3],
        sp.sqrt(2980198): symbols[0] * symbols[2] * symbols[3],
        sp.sqrt(8940594): symbols[0] * symbols[1] * symbols[2] * symbols[3],
        sp.sqrt(249): symbols[1] * symbols[2],
    }
    dynamic: dict[sp.Expr, sp.Expr] = {}
    for atom in expression.atoms(sp.Pow):
        if (
            atom.exp != sp.Rational(1, 2)
            or not atom.base.is_Rational
            or atom.base <= 0
        ):
            continue
        base = sp.Rational(atom.base)
        coefficient = sp.S.One
        monomial = sp.S.One
        for integer, denominator in ((int(base.p), False), (int(base.q), True)):
            square_part = 1
            square_free = 1
            for prime, exponent in sp.factorint(integer).items():
                square_part *= prime ** (exponent // 2)
                square_free *= prime ** (exponent % 2)
            coefficient = (
                coefficient / square_part
                if denominator
                else coefficient * square_part
            )
            for radical, symbol in zip(
                (2, 3, 83, 17953), symbols, strict=True
            ):
                if square_free % radical == 0:
                    square_free //= radical
                    monomial *= symbol
                    if denominator:
                        coefficient /= radical
            if square_free != 1:
                raise ValueError(f"unrecognized radical in {atom}: {square_free}")
        dynamic[atom] = coefficient * monomial
    polynomial = sp.Poly(
        sp.expand(expression.xreplace(dynamic | replacements)),
        *symbols,
        domain=sp.QQ,
    )
    result = _Tower()
    for exponents, coefficient in polynomial.terms():
        coefficient = sp.Rational(coefficient)
        rational = Fraction(int(coefficient.p), int(coefficient.q))
        mask = 0
        for index, exponent in enumerate(exponents):
            rational *= _Tower.base_squares[index] ** (exponent // 2)
            if exponent % 2:
                mask |= 1 << index
        result += _Tower({mask: rational})
    return result


def _matrix(rows: int, columns: int, entry=None):
    return [
        [entry(i, j) if entry else _Tower() for j in range(columns)]
        for i in range(rows)
    ]


def _convert(matrix: sp.MatrixBase):
    return _matrix(matrix.rows, matrix.cols, lambda i, j: _embed(matrix[i, j]))


def _add(left, right):
    return _matrix(
        len(left), len(left[0]), lambda i, j: left[i][j] + right[i][j]
    )


def _scale(value: _Tower, matrix):
    return _matrix(
        len(matrix), len(matrix[0]), lambda i, j: value * matrix[i][j]
    )


def _multiply(left, right):
    return _matrix(
        len(left),
        len(right[0]),
        lambda i, j: sum(
            (left[i][k] * right[k][j] for k in range(len(right))), _Tower()
        ),
    )


def _transpose(matrix):
    return _matrix(len(matrix[0]), len(matrix), lambda i, j: matrix[j][i])


def _horizontal_stack(columns):
    return [[columns[j][i][0] for j in range(len(columns))] for i in range(4)]


def _zero_matrix(matrix) -> bool:
    return all(value.is_zero for row in matrix for value in row)


def _matrix_jet(expression, coordinates, point):
    return (
        _simplify_matrix(expression.subs(point)),
        tuple(
            _simplify_matrix(expression.diff(coordinate).subs(point))
            for coordinate in coordinates
        ),
    )


def _jet_multiply(left, right):
    value_left, derivative_left = left
    value_right, derivative_right = right
    return (
        _simplify_matrix(value_left * value_right),
        tuple(
            _simplify_matrix(
                derivative_left[k] * value_right
                + value_left * derivative_right[k]
            )
            for k in range(4)
        ),
    )


def _scalar_inverse(jet):
    value, derivative = jet
    return sp.simplify(1 / value), tuple(
        sp.simplify(-entry / value**2) for entry in derivative
    )


def _scalar_sqrt(jet):
    value, derivative = jet
    root = sp.sqrt(value)
    return root, tuple(sp.simplify(entry / (2 * root)) for entry in derivative)


def _scalar_multiply(left, right):
    return sp.simplify(left[0] * right[0]), tuple(
        sp.simplify(left[1][k] * right[0] + left[0] * right[1][k])
        for k in range(4)
    )


def _scalar_scale(constant, jet):
    return sp.simplify(constant * jet[0]), tuple(
        sp.simplify(constant * entry) for entry in jet[1]
    )


def _vector_add(left, right):
    return _simplify_matrix(left[0] + right[0]), tuple(
        _simplify_matrix(left[1][k] + right[1][k]) for k in range(4)
    )


def _vector_scale(scalar, vector):
    return _simplify_matrix(scalar[0] * vector[0]), tuple(
        _simplify_matrix(scalar[1][k] * vector[0] + scalar[0] * vector[1][k])
        for k in range(4)
    )


def _pair(left, metric, right):
    value_left, derivative_left = left
    value_metric, derivative_metric = metric
    value_right, derivative_right = right
    return sp.simplify((value_left.T * value_metric * value_right)[0]), tuple(
        sp.simplify(
            (
                derivative_left[k].T * value_metric * value_right
                + value_left.T * derivative_metric[k] * value_right
                + value_left.T * value_metric * derivative_right[k]
            )[0]
        )
        for k in range(4)
    )


def replacement_fourth_order_tower_certificate(
    coordinates: tuple[sp.Symbol, ...],
    metric_expression: sp.ImmutableMatrix,
    scalar_expression: sp.Expr,
    potential: tuple[sp.Expr, ...],
    scalar_closure: dict[str, object],
    physical_active: dict[str, object],
) -> dict[str, object]:
    """Evaluate the selected point/channel in its exact quadratic tower."""
    time, radius, theta, azimuth = coordinates
    point = {
        time: sp.S.Zero,
        radius: sp.Rational(3, 2),
        theta: sp.pi / 4,
        azimuth: sp.S.Zero,
    }
    identity = sp.eye(4)
    metric = _matrix_jet(metric_expression, coordinates, point)
    inverse_value = _simplify_matrix(metric[0].inv())
    inverse = (
        inverse_value,
        tuple(
            _simplify_matrix(-inverse_value * metric[1][k] * inverse_value)
            for k in range(4)
        ),
    )
    if not (
        scalar_closure["selected_value_matches_physical"]
        and scalar_closure["selected_first_jet_matches_physical"]
    ):
        raise AssertionError("literal selected scalar one-jet bridge failed")

    mixed_ricci = (
        scalar_closure["mixed_ricci_at_point"],
        tuple(scalar_closure["mixed_ricci_first_jets"]),
    )
    # The preceding exact bridge permits this compact physical representative.
    scalar_covector = _matrix_jet(
        sp.ImmutableMatrix(
            [sp.diff(scalar_expression, coordinate) for coordinate in coordinates]
        ),
        coordinates,
        point,
    )
    raised_scalar = _jet_multiply(inverse, scalar_covector)
    scalar_part = (
        _simplify_matrix(raised_scalar[0] * scalar_covector[0].T / 2),
        tuple(
            _simplify_matrix(
                (
                    raised_scalar[1][k] * scalar_covector[0].T
                    + raised_scalar[0] * scalar_covector[1][k].T
                )
                / 2
            )
            for k in range(4)
        ),
    )
    residual = (
        _simplify_matrix(mixed_ricci[0] - scalar_part[0]),
        tuple(
            _simplify_matrix(mixed_ricci[1][k] - scalar_part[1][k])
            for k in range(4)
        ),
    )

    fiber_norm = (radius**3 * sp.sin(theta) ** 2 + radius + 2) / radius
    raw_field = sp.ImmutableMatrix(
        4,
        4,
        lambda i, j: sp.diff(potential[j], coordinates[i])
        - sp.diff(potential[i], coordinates[j]),
    )
    physical_field = _matrix_jet(
        _simplify_matrix(fiber_norm ** sp.Rational(3, 4) * raw_field / sp.sqrt(2)),
        coordinates,
        point,
    )
    core = _jet_multiply(
        _jet_multiply(_jet_multiply(inverse, physical_field), inverse),
        physical_field,
    )
    physical_stress = (
        _simplify_matrix(-core[0] + sp.trace(core[0]) * identity / 4),
        tuple(
            _simplify_matrix(
                -core[1][k] + sp.trace(core[1][k]) * identity / 4
            )
            for k in range(4)
        ),
    )
    residual_jet_bridge = [
        all(sp.simplify(entry) == 0 for entry in residual[0] - physical_stress[0])
    ] + [
        all(
            sp.simplify(entry) == 0
            for entry in residual[1][k] - physical_stress[1][k]
        )
        for k in range(4)
    ]
    if not all(residual_jet_bridge):
        raise AssertionError("literal residual one-jet bridge failed")
    residual = physical_stress

    q_squared = (
        scalar_closure["q_sq_at_point"],
        tuple(scalar_closure["q_sq_first_jet"]),
    )
    q = _scalar_sqrt(q_squared)
    residual_over_q = (
        _simplify_matrix(residual[0] / q[0]),
        tuple(
            _simplify_matrix(
                residual[1][k] / q[0]
                - residual[0] * q[1][k] / q[0] ** 2
            )
            for k in range(4)
        ),
    )
    minus_projector = (
        _simplify_matrix((identity - residual_over_q[0]) / 2),
        tuple(_simplify_matrix(-entry / 2) for entry in residual_over_q[1]),
    )
    plus_projector = (
        _simplify_matrix((identity + residual_over_q[0]) / 2),
        tuple(_simplify_matrix(entry / 2) for entry in residual_over_q[1]),
    )

    def column(jet, index):
        return _simplify_matrix(jet[0][:, index]), tuple(
            _simplify_matrix(jet[1][k][:, index]) for k in range(4)
        )

    timelike = column(minus_projector, 1)
    companion = column(minus_projector, 0)
    timelike_norm = _pair(timelike, metric, timelike)
    remainder = _vector_add(
        companion,
        _vector_scale(
            _scalar_scale(
                -1,
                _scalar_multiply(
                    _pair(timelike, metric, companion),
                    _scalar_inverse(timelike_norm),
                ),
            ),
            timelike,
        ),
    )
    spacelike = column(plus_projector, 0)
    companion_two = column(plus_projector, 1)
    spacelike_norm = _pair(spacelike, metric, spacelike)
    remainder_two = _vector_add(
        companion_two,
        _vector_scale(
            _scalar_scale(
                -1,
                _scalar_multiply(
                    _pair(spacelike, metric, companion_two),
                    _scalar_inverse(spacelike_norm),
                ),
            ),
            spacelike,
        ),
    )
    remainder_norm = _pair(remainder, metric, remainder)
    remainder_two_norm = _pair(remainder_two, metric, remainder_two)
    norm_zero = _scalar_scale(-1, timelike_norm)
    norm_one = remainder_norm
    norm_two = spacelike_norm
    norm_three = remainder_two_norm
    amplitude_squared = _scalar_scale(2, q)
    mixed_zero_three = sp.Rational(243, 143624) * sp.sqrt(2980198)
    mixed_one_two = sp.Rational(89, 35906) * sp.sqrt(53859)
    if sp.simplify(norm_zero[0] * norm_three[0] - mixed_zero_three**2) != 0:
        raise AssertionError("unexpected selected-frame radical relation")
    if sp.simplify(norm_one[0] * norm_two[0] - mixed_one_two**2) != 0:
        raise AssertionError("unexpected selected-frame radical relation")

    _Tower.extension_relations = (
        _embed(norm_zero[0]).coefficients,
        _embed(norm_one[0]).coefficients,
        _embed(amplitude_squared[0]).coefficients,
    )
    _Tower._multiply_masks.cache_clear()
    root_zero, root_one, amplitude = (
        _Tower.generator(index) for index in (4, 5, 6)
    )
    if not (root_zero * root_zero - _embed(norm_zero[0])).is_zero:
        raise AssertionError("first extension relation failed")
    if not (root_one * root_one - _embed(norm_one[0])).is_zero:
        raise AssertionError("second extension relation failed")
    if not (amplitude * amplitude - _embed(amplitude_squared[0])).is_zero:
        raise AssertionError("third extension relation failed")
    base_generators = tuple(_Tower.generator(index) for index in range(4))
    sample_left = root_zero + base_generators[0] * root_one + 2
    sample_middle = root_one + base_generators[1] * amplitude - 3
    sample_right = amplitude + base_generators[2] * base_generators[3] + 5
    tower_ring_laws_exact = all(
        value.is_zero
        for value in (
            sample_left * sample_middle - sample_middle * sample_left,
            (sample_left * sample_middle) * sample_right
            - sample_left * (sample_middle * sample_right),
            sample_left * (sample_middle + sample_right)
            - sample_left * sample_middle
            - sample_left * sample_right,
        )
    )
    if not tower_ring_laws_exact:
        raise AssertionError("quadratic quotient regression law failed")

    def normalize(vector, norm, inverse_root):
        value = _convert(vector[0])
        derivatives = tuple(_convert(entry) for entry in vector[1])
        inverse_root_derivatives = tuple(
            inverse_root * _embed(-norm[1][k] / (2 * norm[0]))
            for k in range(4)
        )
        return (
            _scale(inverse_root, value),
            tuple(
                _add(
                    _scale(inverse_root_derivatives[k], value),
                    _scale(inverse_root, derivatives[k]),
                )
                for k in range(4)
            ),
        )

    columns = (
        normalize(timelike, norm_zero, root_zero * _embed(1 / norm_zero[0])),
        normalize(remainder, norm_one, root_one * _embed(1 / norm_one[0])),
        normalize(spacelike, norm_two, root_one * _embed(1 / mixed_one_two)),
        normalize(
            remainder_two,
            norm_three,
            root_zero * _embed(1 / mixed_zero_three),
        ),
    )
    tetrad = _horizontal_stack([column_jet[0] for column_jet in columns])
    tetrad_derivatives = tuple(
        _horizontal_stack([column_jet[1][k] for column_jet in columns])
        for k in range(4)
    )
    minkowski = _matrix(
        4,
        4,
        lambda i, j: _Tower.rational((-1 if i == 0 else 1) if i == j else 0),
    )
    metric_value = _convert(metric[0])
    orientation = _matrix(
        4,
        4,
        lambda i, j: _Tower.rational((1 if i < 3 else -1) if i == j else 0),
    )
    orthonormal_obstruction = _add(
        _multiply(_multiply(_transpose(tetrad), metric_value), tetrad),
        _scale(_Tower.rational(-1), minkowski),
    )
    base_inverse = _multiply(_multiply(minkowski, _transpose(tetrad)), metric_value)
    coframe = _multiply(orientation, base_inverse)
    inverse_coframe = _multiply(tetrad, orientation)
    tower_identity = _matrix(
        4,
        4,
        lambda i, j: _Tower.rational(1 if i == j else 0),
    )
    inverse_obstruction = _add(
        _multiply(coframe, inverse_coframe),
        _scale(_Tower.rational(-1), tower_identity),
    )
    inverse_derivatives = tuple(
        _scale(
            _Tower.rational(-1),
            _multiply(_multiply(base_inverse, tetrad_derivatives[k]), base_inverse),
        )
        for k in range(4)
    )
    coframe_derivatives = tuple(
        _multiply(orientation, derivative) for derivative in inverse_derivatives
    )

    inverse_amplitude = amplitude * _embed(1 / amplitude_squared[0])
    amplitude_derivatives = tuple(
        _embed(q[1][k]) * inverse_amplitude for k in range(4)
    )

    def canonical(value, hodge=False):
        matrix = _matrix(4, 4)
        i, j = (2, 3) if hodge else (0, 1)
        matrix[i][j] = value
        matrix[j][i] = -value
        return matrix

    canonical_field = canonical(amplitude)
    canonical_hodge = canonical(amplitude, hodge=True)
    canonical_field_derivatives = tuple(
        canonical(value) for value in amplitude_derivatives
    )
    canonical_hodge_derivatives = tuple(
        canonical(value, hodge=True) for value in amplitude_derivatives
    )

    def transported_derivative(canonical_value, canonical_derivatives, direction):
        return _add(
            _add(
                _multiply(
                    _multiply(_transpose(coframe_derivatives[direction]), canonical_value),
                    coframe,
                ),
                _multiply(
                    _multiply(_transpose(coframe), canonical_derivatives[direction]),
                    coframe,
                ),
            ),
            _multiply(
                _multiply(_transpose(coframe), canonical_value),
                coframe_derivatives[direction],
            ),
        )

    field_derivatives = tuple(
        transported_derivative(
            canonical_field, canonical_field_derivatives, direction
        )
        for direction in range(4)
    )
    hodge_derivatives = tuple(
        transported_derivative(
            canonical_hodge, canonical_hodge_derivatives, direction
        )
        for direction in range(4)
    )

    def exterior(derivatives, i, j, k):
        return derivatives[i][j][k] + derivatives[j][k][i] + derivatives[k][i][j]

    def pull(derivatives, a, b, c):
        return sum(
            (
                inverse_coframe[i][a]
                * inverse_coframe[j][b]
                * inverse_coframe[k][c]
                * exterior(derivatives, i, j, k)
                for i, j, k in product(range(4), repeat=3)
            ),
            _Tower(),
        )

    channels = (
        {
            (a, b, c): pull(field_derivatives, a, b, c)
            for a, b, c in product(range(4), repeat=3)
        },
        {
            (a, b, c): pull(hodge_derivatives, a, b, c)
            for a, b, c in product(range(4), repeat=3)
        },
    )
    scalar_coordinate = [
        [_embed(sp.diff(scalar_expression, coordinate).subs(point))]
        for coordinate in coordinates
    ]
    scalar_principal = tuple(
        entry[0] for entry in _multiply(_transpose(inverse_coframe), scalar_coordinate)
    )
    eta = (
        -channels[0][0, 2, 3] * inverse_amplitude,
        -channels[0][1, 2, 3] * inverse_amplitude,
        channels[1][0, 1, 2] * inverse_amplitude,
        channels[1][0, 1, 3] * inverse_amplitude,
    )
    cosine = _embed(5 * sp.sqrt(53859) / 17953)
    cosine_quotient_residual = (
        -2 * channels[1][0, 2, 3]
        - cosine * amplitude * scalar_principal[0]
    )

    def wedge(one_form, two_form, a, b, c):
        return (
            one_form[a] * two_form[b][c]
            + one_form[b] * two_form[c][a]
            + one_form[c] * two_form[a][b]
        )

    channel_residuals: dict[tuple[int, int, int, int], _Tower] = {}
    for channel_index, channel in enumerate(channels):
        for a, b, c in product(range(4), repeat=3):
            expected = (
                cosine
                * wedge(scalar_principal, canonical_field, a, b, c)
                * _Tower.rational(sp.Rational(1, 2))
                - wedge(eta, canonical_hodge, a, b, c)
                if channel_index == 0
                else wedge(eta, canonical_field, a, b, c)
                - cosine
                * wedge(scalar_principal, canonical_hodge, a, b, c)
                * _Tower.rational(sp.Rational(1, 2))
            )
            difference = channel[a, b, c] - expected
            if not difference.is_zero:
                channel_residuals[channel_index, a, b, c] = difference

    reflection = (
        -scalar_principal[0],
        -scalar_principal[1],
        scalar_principal[2],
        scalar_principal[3],
    )
    active_wedge_components = {
        (left, right): eta[left] * reflection[right]
        - eta[right] * reflection[left]
        for left in range(4)
        for right in range(left + 1, 4)
    }
    active_wedge = active_wedge_components[0, 3]
    other_active_wedge_components_zero = all(
        value.is_zero
        for component, value in active_wedge_components.items()
        if component != (0, 3)
    )

    # This is the physical EMD derivative, not yet the independently derived
    # derivative of the literal curvature quotient field.
    physical_dA_coordinate = tuple(
        physical_active["physical_cosine_coupling_derivative_at_point"]
    )
    expected_physical_dA = (
        sp.S.Zero,
        -sp.Rational(3999888, 322310209) * sp.sqrt(53859),
        sp.Rational(5869152, 322310209) * sp.sqrt(53859),
        sp.S.Zero,
    )
    physical_dA_exact = all(
        sp.simplify(value - expected) == 0
        for value, expected in zip(
            physical_dA_coordinate, expected_physical_dA, strict=True
        )
    )
    physical_dA_principal = tuple(
        entry[0]
        for entry in _multiply(
            _transpose(inverse_coframe),
            [[_embed(value)] for value in physical_dA_coordinate],
        )
    )
    sine = _embed(18 * sp.sqrt(2980198) / 17953)
    sine_quotient_residual = -(
        physical_dA_principal[0] * reflection[3]
        - physical_dA_principal[3] * reflection[0]
    ) - 2 * sine * active_wedge
    next_order_residual = tuple(
        physical_dA_principal[index]
        + 2 * sine * eta[index]
        - sine * sine * reflection[index]
        for index in range(4)
    )
    output_residual = cosine * cosine + sine * sine - 3

    coframe_inverse_exact = _zero_matrix(inverse_obstruction)
    source_square = scalar_principal[0] * scalar_principal[0]
    source_square_coefficients = source_square.coefficients
    source_square_is_positive = (
        set(source_square_coefficients) == {7, 15}
        and source_square_coefficients[7] < 0
        and source_square_coefficients[15] > 0
        and source_square_coefficients[15] ** 2
            * _Tower.base_squares[3]
            > source_square_coefficients[7] ** 2
    )
    source_nonzero_from_positive_square = (
        source_square_is_positive and coframe_inverse_exact
    )
    active_wedge_nonzero_from_physical_bridge = (
        bool(physical_active["active"])
        and coframe_inverse_exact
        and not channel_residuals
        and all(residual_jet_bridge)
        and _tower_square_is_positive_rational(active_wedge)
    )
    tower_payload = [
        *(entry for row in orthonormal_obstruction for entry in row),
        *(entry for row in inverse_obstruction for entry in row),
        *(channels[channel_index][component]
          for channel_index in range(2)
          for component in sorted(channels[channel_index])),
        *scalar_principal,
        *eta,
        *reflection,
        *active_wedge_components.values(),
        cosine_quotient_residual,
        sine_quotient_residual,
        *next_order_residual,
        output_residual,
    ]

    return {
        "tower_slots": 128,
        "tower_dimension_certified": False,
        "tower_ring_laws_exact": tower_ring_laws_exact,
        "tower_relations_sha256": _tower_relations_sha256(),
        "tower_payload_sha256": _tower_payload_sha256(tower_payload),
        "literal_selected_scalar_one_jet_matches_physical": True,
        "literal_residual_one_jet_matches_physical": all(residual_jet_bridge),
        "selected_frame_orthonormal": _zero_matrix(orthonormal_obstruction),
        "selected_coframe_inverse": coframe_inverse_exact,
        "source_component": 0,
        "source_nonzero": source_nonzero_from_positive_square,
        "source_nonzero_bridge": (
            "exact-positive-square-via-rational-sqrt17953-inequality"
        ),
        "source_coefficients": _tower_element_payload(scalar_principal[0]),
        "source_square_coefficients": _tower_element_payload(
            source_square
        ),
        "wedge_component": (0, 3),
        "active_wedge_nonzero": active_wedge_nonzero_from_physical_bridge,
        "active_wedge_nonzero_bridge": (
            "positive-rational-square-plus-exact-physical/invertible-channel-bridge"
        ),
        "active_wedge_representation_nonzero": not active_wedge.is_zero,
        "active_wedge_coefficients": _tower_element_payload(active_wedge),
        "active_wedge_square_coefficients": _tower_element_payload(
            active_wedge * active_wedge
        ),
        "other_active_wedge_components_zero": (
            other_active_wedge_components_zero
        ),
        "cosine_value": "5*sqrt(53859)/17953",
        "literal_cosine_quotient_exact": cosine_quotient_residual.is_zero,
        "complete_channel_residual_count": len(channel_residuals),
        "physical_dA_value": [str(value) for value in physical_dA_coordinate],
        "physical_dA_is_exact_derivative_of_sqrt_three_cosine": physical_dA_exact,
        "sine_value": "18*sqrt(2980198)/17953",
        "physical_dA_sine_quotient_exact": sine_quotient_residual.is_zero,
        "physical_dA_next_order_residuals_exact": all(
            residual.is_zero for residual in next_order_residual
        ),
        "physical_dA_output_three_exact": output_residual.is_zero,
        "literal_quotient_derivative_equals_physical_dA": "not-certified",
    }
