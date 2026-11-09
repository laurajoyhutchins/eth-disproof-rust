"""Symbolic rational-height bounds for the ACTUAL implicit spectral operator.

Source correspondence:
  eth/construction.py::_interpolation_polynomial
  eth/construction.py::_walsh_by_weight
  eth/construction.py::construct_implicit_auxiliary
  eth/construction.py::ImplicitAuxiliaryDesign.row_at
  eth/construction.py::ImplicitAuxiliaryDesign.exceptional_projector_at
  eth/construction.py::construct_from_schedules

This proves an input-parameter polynomial height bound on rational
coefficient VALUES. It never constructs the virtual D=r**(2Q) operator
or its D**2 rows. It does not certify the cost of projector Gram/RREF,
label balancing, measurement row counts, matrix elimination, or
intermediate tensor contraction. Those remain independent obligations.

For a0,...,a0+R-1 in [0,Q], write the exact interpolation polynomial

  f(T)=sum_(k=0)^(R-1) eps*(-2)^k/k! * product_(i=0)^(k-1)(T-a0-i).

Put L=(R-1)! and C=R*(2*(Q+1))**(R-1).
For every integer 0<=j<=Q, L*f(j) is integral and |L*f(j)|<=L*C.
The weight-symmetric Walsh coefficients are signed averages of 2**Q
such values, so each 2**Q*L*beta_s is integral and of magnitude at
most 2**Q*L*C. Summing at most 2**Q Walsh coefficients gives a
kernel numerator bounded by 2**(2Q)*L*C over denominator 2**Q*L.

For a row P=delta + kernel*(prod_(h in S)(1-T/h)-1),
S subset [1,Q], |S|<=R-1, let F=Q!.
The coefficients of F*(prod(1-T/h)-1) are integers and have total
absolute value <= F*2**R. Therefore every row coefficient is an
integer over H=2**Q*(R-1)!*Q!, with absolute numerator <=
H+2**(2Q+R)*(R-1)!*Q!*C.

For the actual transferred CNF replacement, each occurrence/variable
coefficient sums at most ell original rows with the SAME denominator
H, where ell is the input literal-incidence count. Its degree is
at most R-1. These bounds are polynomial in the encoded parameter
bits Q,R,n,ell, even if D and exceptional_count are astronomical.
They say nothing about producing the rows in total bounded time.
"""
from __future__ import annotations

from dataclasses import dataclass


def _ceil_log2_positive(value: int) -> int:
    if value < 1:
        raise ValueError("positive argument required")
    return (value - 1).bit_length()


@dataclass(frozen=True, slots=True)
class ImplicitSpectralHeight:
    r: int
    Q: int
    R: int
    virtual_dimension_bits_upper: int
    replacement_degree_upper: int
    kernel_numerator_bits_upper: int
    kernel_denominator_bits_upper: int
    row_numerator_bits_upper: int
    row_denominator_bits_upper: int
    projector_numerator_bits_upper: int
    projector_denominator_bits_upper: int

    def transferred_numerator_bits_upper(self, occurrences: int) -> int:
        """Each transferred coefficient is a sum of <= occurrences rows."""
        if type(occurrences) is not int or occurrences < 0:
            raise ValueError("occurrences must be nonnegative")
        return self.row_numerator_bits_upper + _ceil_log2_positive(occurrences + 1) + 1


def implicit_spectral_height(r: int, Q: int, R: int) -> ImplicitSpectralHeight:
    """Prove safe coefficient bounds without allocating D or factorials.

    The assumptions are exactly construct_implicit_auxiliary's numerical
    parameter domain. In particular R need not be the paper schedule.
    """
    if any(type(x) is not int for x in (r, Q, R)):
        raise ValueError("r,Q,R must be exact integers")
    if r < 2 or Q < 1 or R < 1 or R > Q + 1:
        raise ValueError("require r>=2, Q>=1, 1<=R<=Q+1")

    # (R-1)! <= R**(R-1), Q! <= Q**Q.
    log_l = (R - 1) * _ceil_log2_positive(R)
    log_f = Q * _ceil_log2_positive(Q)
    # C = R*(2*(Q+1))**(R-1).
    log_c = _ceil_log2_positive(R) + (R - 1) * (
        1 + _ceil_log2_positive(Q + 1)
    )
    # H = 2**Q * (R-1)! * Q!.
    log_h = Q + log_l + log_f
    # |2**Q L kernel| <= 2**(2Q)*L*C.
    kernel_num_bits = 2 * Q + log_l + log_c + 1
    kernel_den_bits = Q + log_l + 1
    # |H [T**j]P| <= H + 2**(2Q+R)*L*F*C.
    log_other = 2 * Q + R + log_l + log_f + log_c
    return ImplicitSpectralHeight(
        r=r,
        Q=Q,
        R=R,
        virtual_dimension_bits_upper=2 * Q * _ceil_log2_positive(r) + 1,
        replacement_degree_upper=R - 1,
        kernel_numerator_bits_upper=kernel_num_bits,
        kernel_denominator_bits_upper=kernel_den_bits,
        row_numerator_bits_upper=max(log_h, log_other) + 2,
        row_denominator_bits_upper=log_h + 1,
        # For a projector, included is a partial coefficient sum of
        # (1+z)**same*(1-z)**swapped, whose l1 norm <= 2**Q.
        # The total is either 0 or 2**same. Its denominator is
        # 2**(same+swapped), giving these uniform bit ceilings.
        projector_numerator_bits_upper=Q + 2,
        projector_denominator_bits_upper=Q + 1,
    )


@dataclass(frozen=True, slots=True)
class ImplicitDeformationOutputHeight:
    """Height of the final H(t+z) before materializing transferred rows."""

    n: int
    m: int
    occurrences: int
    r: int
    Q: int
    R: int
    replacement_coefficient_count_upper: int
    transferred_input_component_bits_upper: int
    output_degree_upper: int
    numerator_bits_upper: int
    denominator_bits_upper: int


def implicit_deformation_output_height(
    n: int, m: int, occurrences: int, *, r: int, Q: int, R: int,
) -> ImplicitDeformationOutputHeight:
    """Compose the implicit row bound with the universal output lemma.

    Applies to the *actual* occurrence transfer, provided n,m,ell are
    its declared input counts and centers are integers from 1..Q.
    No CNF, swap matrix, labels or output coefficients are allocated.
    """
    if any(type(v) is not int or v < 0 for v in (n, m, occurrences)):
        raise ValueError("n,m,occurrences must be nonnegative integers")
    spectral = implicit_spectral_height(r, Q, R)
    degree = R - 1
    K = n * occurrences * R
    b = max(
        spectral.transferred_numerator_bits_upper(occurrences),
        spectral.row_denominator_bits_upper,
        (Q).bit_length(),
        1,
    )
    E = b * (K + degree)
    J = (
        degree
        + _ceil_log2_positive(n * (degree + 1) + 1)
        + _ceil_log2_positive(degree + 1)
    )
    return ImplicitDeformationOutputHeight(
        n=n,
        m=m,
        occurrences=occurrences,
        r=r,
        Q=Q,
        R=R,
        replacement_coefficient_count_upper=K,
        transferred_input_component_bits_upper=b,
        output_degree_upper=occurrences * degree,
        numerator_bits_upper=n + m + occurrences * (E + J) + 1,
        denominator_bits_upper=occurrences * E + 1,
    )
