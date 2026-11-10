"""Quantitative existence of a selector subbasis for projected rowspaces.

Source objects:
  construction._local_eigenvectors / ImplicitAuxiliaryDesign.measurement_at
  construction.construct_from_schedules / balance.choose_balanced_schedules
  parameters.audit_paper_bounds (October 25 Step-5 assumptions)

The projected Gram has precisely the same rational rowspace as the
restricted exceptional selector matrix. A linearly independent subset
of the ORIGINAL selector rows has the same space and preserves each
row's integral L1<=D bound. At most c exceptional selector rows occur
in each copy/group, with c<=D=r**(2Q), and at most h label copies.
Therefore the subset uses <=r*h*c rows per center, exactly the old
selector row-count upper bound. It is not necessary to bound the
primitive Gram rows' L1 to prove the *existence* of such a basis.

If the incidence-balancing lemma proves h*D<=2M, then
   (#rows) <= 2*r*M*(c/D).
The exceptional spectral selector fraction is the tail probability
of Binomial(Q,p), p=(r-1)/(2r), outside the R-point interpolation
interval centered at pQ.

If R>=2 and 6R<=Q, both outside tails are >=(R-1)/2 from
the mean. Hoeffding yields
   c/D <= 2 exp(-R**2/(8Q)) <= 2**(1-floor(R**2/(8Q))).
If R**2>=2048*Q*nu and nu=ceil(log2(lam)), then
   c/D <= 2**(1-256*nu).
Moreover r**2<=lam and lam<=2**nu; M<=3n. Hence
   (r**2 * lam * M / n) * (c/D)
      <= 3*2**(1-254*nu) < 1.
Thus #rows <=2n/(r*lam), the exact quantitative paper bound.

This is an algebraic/existential proof and a constructive algorithm
polynomial in the explicitly enumerated selector rows. On the
manuscript's admitted scale c<=D and D**128<=2n, so enumeration plus
incremental exact row rank is polynomial in n in a mathematical
bit-machine model (with enormous constants). Current implementation
resource caps and the enormous physical input are NOT removed.

The source projector's *specific primitive Gram basis* can still
violate L1<=D. This certificate applies to the selected original
selector rows and must not be passed off as a Gram-basis certificate.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class QuantitativeSelectorCertificate:
    lambda_bits: int
    nu_bits: int
    r: int
    Q: int
    R: int
    # An upper bound on c/D, expressed as 2**tail_dyadic_exponent.
    tail_dyadic_exponent: int
    tail_from_hoeffding_exponent: int
    # Upper bound on (r**2 * lambda * M/n) * (c/D),
    # where M/n<=3, expressed as 3*2**row_ratio_dyadic_exponent.
    row_ratio_dyadic_exponent: int
    row_count_sufficient: bool
    spectral_tail_sufficient: bool
    group_and_label_lemma_required: bool = True
    actual_projected_gram_l1_certified: bool = False


def certify_quantitative_selector_subbasis(
    *, lambda_bits: int, nu_bits: int, r: int, Q: int, R: int,
) -> QuantitativeSelectorCertificate:
    """Derive dyadic row-count inequality WITHOUT instantiating n,D,c.

    Requires a subset of the *exact* Step-5 audit conditions, including
    the interval, tail inequality, and r schedule size. The balancing
    multiplicity h*D<=2M must be supplied separately by the incidence
    lemma; this object never pretends to construct that schedule.
    """
    values = (lambda_bits, nu_bits, r, Q, R)
    if any(type(x) is not int for x in values):
        raise ValueError("paper parameters must be exact integers")
    lam, nu = lambda_bits, nu_bits
    if (lam < 2 or nu < 1 or nu != (lam - 1).bit_length()
            or r < 2 or r*r > lam or Q < 1 or R < 32
            or Q < 6 * R or R > Q + 1):
        raise ValueError("quantitative selector premises not satisfied")
    if R * R < 2048 * Q * nu:
        raise ValueError("spectral-tail sufficient inequality not satisfied")

    # In the source a0 = floor(mu - (R-1)/2); with 6R<=Q
    # and 1/4<=p<1/2 it is an interior interval (no clamp).
    # For R>=2, (R-1)^2/(2Q) >= R^2/(8Q).
    # Hoeffding and exp(-x)<=2^(-x) produce this dyadic bound.
    hoeffding_exp = 1 - (R * R) // (8 * Q)
    sufficient_exp = 1 - 256 * nu
    if hoeffding_exp > sufficient_exp:
        raise ArithmeticError("source tail bound fails Step-5 inequality")

    # r^2*lam*(M/n)<=3*(2^nu)^2. The row-count ratio is
    # bounded by 3*2**(2nu+hoeffding_exp).
    ratio_exp = 2 * nu + hoeffding_exp
    # If ratio_exp<=-2 then 3*2**ratio_exp <=3/4 <1.
    return QuantitativeSelectorCertificate(
        lambda_bits=lam, nu_bits=nu, r=r, Q=Q, R=R,
        tail_dyadic_exponent=sufficient_exp,
        tail_from_hoeffding_exponent=hoeffding_exp,
        row_ratio_dyadic_exponent=ratio_exp,
        row_count_sufficient=ratio_exp <= -2,
        spectral_tail_sufficient=hoeffding_exp <= sufficient_exp,
    )
