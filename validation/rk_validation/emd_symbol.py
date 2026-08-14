"""Exact principal-symbol and prolongation algebra for four-dimensional EMD.

The source-free Einstein--Maxwell--dilaton equations are written in potential
variables ``(g, A, phi)``.  At a normal-coordinate point with
``g = diag(-1, 1, 1, 1)`` their order-two principal symbol is block diagonal:

* the linearized Ricci symbol on a symmetric two-tensor;
* the ``div d`` symbol on a one-form potential; and
* the scalar wave symbol.

All coupling- and matter-dependent terms are lower order.  Consequently this
calculation applies at the repository's active witness (where ``phi = 0``),
and in an orthonormal frame at every Lorentzian EMD jet.

The routines below construct the symbol matrices and their prolongations over
the rationals.  They also construct the contracted-Bianchi and Maxwell-gauge
row syzygies.  No numerical rank decisions are made.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import cache
import hashlib
from itertools import combinations_with_replacement
from typing import Iterable, Mapping, Sequence

import sympy as sp
from sympy.polys.matrices import DomainMatrix


DIMENSION = 4
MINKOWSKI_DIAGONAL = (-1, 1, 1, 1)

MultiIndex = tuple[int, ...]
FieldLabel = str
EquationLabel = str
FirstSyzygy = Mapping[tuple[int, int], sp.Rational]


def symmetric_multiindices(degree: int) -> tuple[MultiIndex, ...]:
    """Return the lexicographic symmetric derivative basis of given degree."""

    if degree < 0:
        raise ValueError("degree must be nonnegative")
    return tuple(combinations_with_replacement(range(DIMENSION), degree))


def _pair(left: int, right: int) -> tuple[int, int]:
    return (left, right) if left <= right else (right, left)


def _merge(left: MultiIndex, right: MultiIndex) -> MultiIndex:
    return tuple(sorted((*left, *right)))


def _rational(value: sp.Expr | int) -> sp.Rational:
    result = sp.Rational(value)
    if not result.is_Rational:
        raise ValueError(f"coefficient is not rational: {value}")
    return result


@dataclass(frozen=True)
class SymbolSector:
    """One block of an order-two symbol and its first differential identities."""

    name: str
    fields: tuple[FieldLabel, ...]
    equations: tuple[EquationLabel, ...]
    principal: sp.ImmutableSparseMatrix
    first_syzygies: tuple[FirstSyzygy, ...]

    def __post_init__(self) -> None:
        expected_columns = len(self.fields) * len(symmetric_multiindices(2))
        if self.principal.shape != (len(self.equations), expected_columns):
            raise ValueError("principal-symbol shape does not match labels")


@dataclass(frozen=True)
class ProlongedSymbol:
    """A rational symbol matrix with explicit row and column labels."""

    sector_name: str
    prolongation_degree: int
    matrix: sp.ImmutableSparseMatrix
    row_labels: tuple[tuple[EquationLabel, MultiIndex], ...]
    column_labels: tuple[tuple[FieldLabel, MultiIndex], ...]

    @property
    def jet_order(self) -> int:
        return 2 + self.prolongation_degree


def _column_labels(
    fields: Sequence[FieldLabel], degree: int
) -> tuple[tuple[FieldLabel, MultiIndex], ...]:
    derivatives = symmetric_multiindices(degree)
    return tuple((field, derivative) for field in fields for derivative in derivatives)


def _mutable_principal(
    fields: Sequence[FieldLabel], equations: Sequence[EquationLabel]
) -> tuple[
    sp.MutableSparseMatrix,
    dict[tuple[FieldLabel, MultiIndex], int],
]:
    labels = _column_labels(fields, 2)
    return (
        sp.MutableSparseMatrix.zeros(len(equations), len(labels)),
        {label: index for index, label in enumerate(labels)},
    )


def _add_coefficient(
    matrix: sp.MutableSparseMatrix,
    column_index: Mapping[tuple[FieldLabel, MultiIndex], int],
    row: int,
    field: FieldLabel,
    derivative: Iterable[int],
    coefficient: sp.Expr | int,
) -> None:
    multiindex = tuple(sorted(derivative))
    column = column_index[(field, multiindex)]
    matrix[row, column] += _rational(coefficient)


def ricci_sector() -> SymbolSector:
    """Linearized Ricci symbol in covariant metric components.

    With ``epsilon_r = (-1, 1, 1, 1)``, the formula is

    ``2 Ric_mn = sum_r epsilon_r
       (h_rn,rm + h_rm,rn - h_mn,rr - h_rr,mn)``.
    """

    pairs = tuple(combinations_with_replacement(range(DIMENSION), 2))
    fields = tuple(f"g{left}{right}" for left, right in pairs)
    equations = tuple(f"Ric{left}{right}" for left, right in pairs)
    field_for_pair = {
        pair: fields[index]
        for index, pair in enumerate(pairs)
    }
    equation_for_pair = {
        pair: index
        for index, pair in enumerate(pairs)
    }
    matrix, columns = _mutable_principal(fields, equations)

    for m, n in pairs:
        row = equation_for_pair[(m, n)]
        for r, sign in enumerate(MINKOWSKI_DIAGONAL):
            coefficient = sp.Rational(sign, 2)
            _add_coefficient(
                matrix, columns, row, field_for_pair[_pair(r, n)], (r, m), coefficient
            )
            _add_coefficient(
                matrix, columns, row, field_for_pair[_pair(r, m)], (r, n), coefficient
            )
            _add_coefficient(
                matrix, columns, row, field_for_pair[(m, n)], (r, r), -coefficient
            )
            _add_coefficient(
                matrix, columns, row, field_for_pair[(r, r)], (m, n), -coefficient
            )

    # Contracted Bianchi: d^m Ric_mn - (1/2) d_n tr(Ric) = 0.
    syzygies: list[dict[tuple[int, int], sp.Rational]] = []
    for n in range(DIMENSION):
        relation: dict[tuple[int, int], sp.Rational] = {}
        for m, sign in enumerate(MINKOWSKI_DIAGONAL):
            key = (equation_for_pair[_pair(m, n)], m)
            relation[key] = relation.get(key, sp.S.Zero) + sp.Rational(sign)
        for r, sign in enumerate(MINKOWSKI_DIAGONAL):
            key = (equation_for_pair[(r, r)], n)
            relation[key] = relation.get(key, sp.S.Zero) - sp.Rational(sign, 2)
        syzygies.append({key: value for key, value in relation.items() if value != 0})

    return SymbolSector(
        name="linearized-Ricci",
        fields=fields,
        equations=equations,
        principal=sp.ImmutableSparseMatrix(matrix),
        first_syzygies=tuple(syzygies),
    )


def maxwell_sector() -> SymbolSector:
    """The Lorentzian ``div d`` symbol on a covariant potential one-form."""

    fields = tuple(f"A{index}" for index in range(DIMENSION))
    equations = tuple(f"Maxwell{index}" for index in range(DIMENSION))
    matrix, columns = _mutable_principal(fields, equations)

    for n in range(DIMENSION):
        for m, sign in enumerate(MINKOWSKI_DIAGONAL):
            _add_coefficient(matrix, columns, n, fields[n], (m, m), sign)
            _add_coefficient(matrix, columns, n, fields[m], (m, n), -sign)

    # Gauge identity: d^n (div d A)_n = 0.
    relation = {
        (index, index): sp.Rational(sign)
        for index, sign in enumerate(MINKOWSKI_DIAGONAL)
    }
    return SymbolSector(
        name="Maxwell-potential",
        fields=fields,
        equations=equations,
        principal=sp.ImmutableSparseMatrix(matrix),
        first_syzygies=(relation,),
    )


def scalar_sector() -> SymbolSector:
    """The scalar Lorentzian wave symbol."""

    fields = ("phi",)
    equations = ("wave",)
    matrix, columns = _mutable_principal(fields, equations)
    for index, sign in enumerate(MINKOWSKI_DIAGONAL):
        _add_coefficient(matrix, columns, 0, "phi", (index, index), sign)
    return SymbolSector(
        name="scalar-wave",
        fields=fields,
        equations=equations,
        principal=sp.ImmutableSparseMatrix(matrix),
        first_syzygies=(),
    )


def direct_sum_sector(sectors: Sequence[SymbolSector]) -> SymbolSector:
    """Form the block direct sum while transporting first syzygies."""

    if not sectors:
        raise ValueError("at least one sector is required")
    fields = tuple(field for sector in sectors for field in sector.fields)
    equations = tuple(equation for sector in sectors for equation in sector.equations)
    derivative_count = len(symmetric_multiindices(2))
    matrix = sp.MutableSparseMatrix.zeros(
        len(equations), len(fields) * derivative_count
    )
    syzygies: list[dict[tuple[int, int], sp.Rational]] = []
    row_offset = 0
    field_offset = 0
    for sector in sectors:
        for (row, column), value in sector.principal.todok().items():
            local_field, derivative = divmod(column, derivative_count)
            target_column = (field_offset + local_field) * derivative_count + derivative
            matrix[row_offset + row, target_column] = value
        for relation in sector.first_syzygies:
            syzygies.append(
                {
                    (row_offset + equation, direction): coefficient
                    for (equation, direction), coefficient in relation.items()
                }
            )
        row_offset += len(sector.equations)
        field_offset += len(sector.fields)
    return SymbolSector(
        name="EMD-potential",
        fields=fields,
        equations=equations,
        principal=sp.ImmutableSparseMatrix(matrix),
        first_syzygies=tuple(syzygies),
    )


def emd_potential_sector() -> SymbolSector:
    """The full order-two EMD principal symbol at a Lorentzian point."""

    return direct_sum_sector((ricci_sector(), maxwell_sector(), scalar_sector()))


def prolong_symbol(sector: SymbolSector, degree: int) -> ProlongedSymbol:
    """Prolong an order-two constant-coefficient symbol ``degree`` times."""

    if degree < 0:
        raise ValueError("prolongation degree must be nonnegative")
    base_derivatives = symmetric_multiindices(2)
    prolonging_derivatives = symmetric_multiindices(degree)
    target_derivatives = symmetric_multiindices(2 + degree)
    base_columns = _column_labels(sector.fields, 2)
    column_labels = _column_labels(sector.fields, 2 + degree)
    target_columns = {label: index for index, label in enumerate(column_labels)}
    row_labels = tuple(
        (equation, derivative)
        for equation in sector.equations
        for derivative in prolonging_derivatives
    )
    matrix = sp.MutableSparseMatrix.zeros(len(row_labels), len(column_labels))
    base_nonzero = tuple(sector.principal.todok().items())

    for equation_index in range(len(sector.equations)):
        terms = (
            (base_columns[column], coefficient)
            for (row, column), coefficient in base_nonzero
            if row == equation_index
        )
        equation_terms = tuple(terms)
        for derivative_index, derivative in enumerate(prolonging_derivatives):
            row = equation_index * len(prolonging_derivatives) + derivative_index
            for (field, base_derivative), coefficient in equation_terms:
                column = target_columns[(field, _merge(base_derivative, derivative))]
                matrix[row, column] += coefficient

    # Retain the local variable to make the derivative-basis convention
    # explicit and guard accidental changes to the order-two layout.
    if len(base_derivatives) * len(sector.fields) != sector.principal.cols:
        raise AssertionError("inconsistent base derivative basis")
    return ProlongedSymbol(
        sector_name=sector.name,
        prolongation_degree=degree,
        matrix=sp.ImmutableSparseMatrix(matrix),
        row_labels=row_labels,
        column_labels=column_labels,
    )


def exact_rank(matrix: sp.MatrixBase) -> int:
    """Compute rank by exact domain linear algebra (never numerical SVD)."""

    domain_matrix = DomainMatrix.from_Matrix(matrix).to_field()
    return int(domain_matrix.rank())


def nullity(matrix: sp.MatrixBase) -> int:
    return matrix.cols - exact_rank(matrix)


def cartan_flag_dimensions(sector: SymbolSector) -> tuple[int, ...]:
    """Dimensions along the standard flag used for Cartan characters.

    At step ``i`` only derivatives whose indices lie in
    ``{i, ..., 3}`` remain.  Equivalently, this intersects the symbol with
    ``S^2(ann span(e_0,...,e_{i-1})) tensor E``.
    """

    symbol = prolong_symbol(sector, 0)
    dimensions: list[int] = []
    all_rows = tuple(range(symbol.matrix.rows))
    for step in range(DIMENSION + 1):
        selected = tuple(
            index
            for index, (_, derivative) in enumerate(symbol.column_labels)
            if all(direction >= step for direction in derivative)
        )
        if not selected:
            dimensions.append(0)
            continue
        restricted = symbol.matrix.extract(all_rows, selected)
        dimensions.append(len(selected) - exact_rank(restricted))
    return tuple(dimensions)


def cartan_characters(sector: SymbolSector) -> tuple[int, ...]:
    dimensions = cartan_flag_dimensions(sector)
    return tuple(
        dimensions[index] - dimensions[index + 1]
        for index in range(DIMENSION)
    )


def cartan_predicted_nullity(characters: Sequence[int], degree: int) -> int:
    """Hilbert growth predicted by order-two Cartan characters."""

    if degree < 0:
        raise ValueError("degree must be nonnegative")
    if len(characters) != DIMENSION:
        raise ValueError("expected four Cartan characters")
    return sum(
        int(sp.binomial(degree + index - 1, degree)) * character
        for index, character in enumerate(characters, start=1)
    )


def prolonged_first_syzygies(
    sector: SymbolSector, degree: int
) -> sp.ImmutableSparseMatrix:
    """Prolong the first Bianchi/gauge identities to symbol order ``2+degree``.

    The returned rows act on the rows of ``prolong_symbol(sector, degree)``.
    For degree one these are the original identities.  At higher degree each
    identity is differentiated by every symmetric multiindex of degree one
    less.
    """

    if degree < 1:
        raise ValueError("syzygies begin at first prolongation")
    equation_derivatives = symmetric_multiindices(degree)
    equation_derivative_index = {
        derivative: index for index, derivative in enumerate(equation_derivatives)
    }
    outer_derivatives = symmetric_multiindices(degree - 1)
    row_count = len(sector.first_syzygies) * len(outer_derivatives)
    column_count = len(sector.equations) * len(equation_derivatives)
    matrix = sp.MutableSparseMatrix.zeros(row_count, column_count)
    for syzygy_index, relation in enumerate(sector.first_syzygies):
        for outer_index, outer in enumerate(outer_derivatives):
            row = syzygy_index * len(outer_derivatives) + outer_index
            for (equation, direction), coefficient in relation.items():
                derivative = _merge((direction,), outer)
                column = (
                    equation * len(equation_derivatives)
                    + equation_derivative_index[derivative]
                )
                matrix[row, column] += coefficient
    return sp.ImmutableSparseMatrix(matrix)


def syzygies_annihilate_symbol(sector: SymbolSector, degree: int) -> bool:
    relations = prolonged_first_syzygies(sector, degree)
    symbol = prolong_symbol(sector, degree).matrix
    product = relations * symbol
    return not product.todok()


def syzygies_exhaust_left_kernel(sector: SymbolSector, degree: int) -> bool:
    relations = prolonged_first_syzygies(sector, degree)
    symbol = prolong_symbol(sector, degree).matrix
    return (
        syzygies_annihilate_symbol(sector, degree)
        and exact_rank(relations) == symbol.rows - exact_rank(symbol)
    )


def evaluated_covector_symbol(
    sector: SymbolSector, covector: Sequence[int | sp.Expr]
) -> sp.ImmutableSparseMatrix:
    """Evaluate the homogeneous order-two symbol on ``xi tensor xi``."""

    if len(covector) != DIMENSION:
        raise ValueError("expected a four-component covector")
    xi = tuple(_rational(value) for value in covector)
    derivatives = symmetric_multiindices(2)
    matrix = sp.MutableSparseMatrix.zeros(len(sector.equations), len(sector.fields))
    for (row, column), coefficient in sector.principal.todok().items():
        field, derivative_index = divmod(column, len(derivatives))
        derivative = derivatives[derivative_index]
        monomial = xi[derivative[0]] * xi[derivative[1]]
        matrix[row, field] += coefficient * monomial
    return sp.ImmutableSparseMatrix(matrix)


def emd_gauge_amplitudes(
    covector: Sequence[int | sp.Expr],
) -> sp.ImmutableSparseMatrix:
    """Return four infinitesimal-diffeomorphism and one Maxwell-gauge columns.

    The field order agrees with :func:`emd_potential_sector`.  A metric gauge
    amplitude is ``h_mn = xi_m X_n + xi_n X_m`` and the Maxwell gauge
    amplitude is ``A_m = xi_m lambda``.  A background-dependent diffeomorphism
    contribution to ``A`` is itself proportional to ``xi`` at symbol level,
    so it lies in the same five-dimensional span.
    """

    if len(covector) != DIMENSION:
        raise ValueError("expected a four-component covector")
    xi = tuple(_rational(value) for value in covector)
    metric_pairs = tuple(combinations_with_replacement(range(DIMENSION), 2))
    field_count = len(metric_pairs) + DIMENSION + 1
    matrix = sp.MutableSparseMatrix.zeros(field_count, DIMENSION + 1)
    for row, (m, n) in enumerate(metric_pairs):
        for gauge_direction in range(DIMENSION):
            matrix[row, gauge_direction] = (
                xi[m] * int(n == gauge_direction)
                + xi[n] * int(m == gauge_direction)
            )
    potential_offset = len(metric_pairs)
    maxwell_gauge_column = DIMENSION
    for m in range(DIMENSION):
        matrix[potential_offset + m, maxwell_gauge_column] = xi[m]
    return sp.ImmutableSparseMatrix(matrix)


@cache
def coordinate_formula_emd_principal_at_active_lower_jet(
) -> sp.ImmutableSparseMatrix:
    """Extract the highest-jet Jacobian from the full coordinate EMD evaluator.

    This is an independent construction of the principal matrix from
    :func:`rk_validation.exact.emd_residuals_at`.  The background first jet is
    the physical active point used in the project, in radial gauge:

    ``g = diag(-1,1,1,1)``, ``phi = x0 + 2*x2``, and
    ``A = sqrt(2)*(x0 dx1 + x2 dx3)``.

    Thus ``F_01 = F_23 = sqrt(2)``, the unweighted physical normalization of
    the balanced curvature-normalized Maxwell field.  The coupling is kept as
    an exact symbolic real variable; every highest-jet coefficient simplifies
    independently of it, covering both ``a=1`` and ``a=sqrt(3)`` at once.

    Each of the 150 symmetric highest-jet coordinates is switched on by a
    normalized quadratic monomial.  Subtracting the unperturbed residual
    yields the corresponding Jacobian column exactly.  The coordinate
    The evaluator uses the trace-reversed Ricci form of the metric equation,
    which is equivalent in four dimensions to the Einstein-tensor form by an
    invertible target trace reversal and therefore matches ``ricci_sector``.
    It returns the Maxwell equation with an upper free index, so its four rows
    are lowered with the Minkowski metric before comparison.
    """

    # Local import keeps the transparent index-level symbol engine usable on
    # its own and makes this cross-check genuinely travel through the full
    # coordinate residual implementation.
    from rk_validation.exact import emd_residuals_at

    coordinates = sp.symbols("x0:4", real=True)
    coupling = sp.symbols("a", real=True)
    point = dict.fromkeys(coordinates, sp.S.Zero)
    metric_pairs = tuple(combinations_with_replacement(range(DIMENSION), 2))
    derivatives = symmetric_multiindices(2)
    base_metric = sp.ImmutableMatrix(sp.diag(*MINKOWSKI_DIAGONAL))
    base_potential = (
        sp.S.Zero,
        sp.sqrt(2) * coordinates[0],
        sp.S.Zero,
        sp.sqrt(2) * coordinates[2],
    )
    base_scalar = coordinates[0] + 2 * coordinates[2]

    def residual_vector(
        metric: sp.MatrixBase,
        potential: Sequence[sp.Expr],
        scalar: sp.Expr,
    ) -> tuple[sp.Expr, ...]:
        residual = emd_residuals_at(
            coordinates,
            metric,
            scalar,
            potential,
            coupling,
            point,
        )
        return (
            *(residual.einstein[m, n] for m, n in metric_pairs),
            *(
                MINKOWSKI_DIAGONAL[index] * residual.maxwell[index]
                for index in range(DIMENSION)
            ),
            residual.scalar,
        )

    baseline = residual_vector(base_metric, base_potential, base_scalar)
    columns: list[tuple[sp.Rational, ...]] = []

    for field_kind, components in (
        ("metric", metric_pairs),
        ("potential", tuple(range(DIMENSION))),
        ("scalar", (0,)),
    ):
        for component in components:
            for derivative in derivatives:
                metric = sp.MutableDenseMatrix(base_metric)
                potential = list(base_potential)
                scalar = base_scalar
                left, right = derivative
                monomial = coordinates[left] * coordinates[right]
                if left == right:
                    monomial /= 2
                if field_kind == "metric":
                    m, n = component
                    metric[m, n] += monomial
                    if m != n:
                        metric[n, m] += monomial
                elif field_kind == "potential":
                    potential[component] += monomial
                else:
                    scalar += monomial
                perturbed = residual_vector(
                    sp.ImmutableMatrix(metric), tuple(potential), scalar
                )
                columns.append(
                    tuple(
                        _rational(sp.simplify(value - base))
                        for value, base in zip(perturbed, baseline, strict=True)
                    )
                )

    return sp.ImmutableSparseMatrix(
        len(baseline),
        len(columns),
        lambda row, column: columns[column][row],
    )


def sparse_matrix_sha256(matrix: sp.MatrixBase) -> str:
    """Hash shape and every nonzero rational entry in canonical order."""

    entries: list[str] = [f"shape:{matrix.rows}:{matrix.cols}"]
    for (row, column), value in sorted(matrix.todok().items()):
        rational = _rational(value)
        entries.append(f"{row}:{column}:{int(rational.p)}:{int(rational.q)}")
    return hashlib.sha256("\n".join(entries).encode("utf-8")).hexdigest()
