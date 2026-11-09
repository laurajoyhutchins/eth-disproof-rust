"""Conditional bit-work envelope for actual tapered rational Hermite recovery.

Exact, allocation-free schedule accounting. It begins AFTER canonical center jets
have been supplied and does not cover construction, interpolation, arbitrary
Python callbacks, native instruction costs, or process RSS.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import prod
from collections.abc import Sequence


@dataclass(frozen=True, slots=True)
class RecoveryWork:
    M: int
    L: int
    u: int
    p: int
    coordinates: int
    centers: int
    coefficients: int
    max_order: int
    max_center_precision: int
    normalize_pairs: int
    center_scans: int
    binomial_calls: int
    unit_convolution_pairs: int
    reciprocal_pairs: int
    quotient_pairs: int
    ring_powers: int
    ring_multiplies: int
    ring_additions: int
    ring_negations: int
    rational_powers: int
    rational_multiplies: int
    rational_additions: int
    max_scale_bits: int
    max_answer_numerator_bits: int
    max_answer_denominator_bits: int
    center_payload_bits: int
    eager_input_payload_bits: int
    retained_abstract_payload_bits: int

    @property
    def max_rational_bits(self) -> int:
        return max(self.max_answer_numerator_bits, self.max_answer_denominator_bits)

    def schoolbook_bit_work_majorant(self, extension_degree: int) -> int:
        """Loose constructive schoolbook-model majorant, not Python VM steps.

        Uses cubic cost for gcd/division, binary rational powers, O(q) work
        to construct each binomial, and the separate canonical Padic model.
        Actual compiled arithmetic backends are outside this correspondence.
        """
        from reference.nested_ring_bit_cost import finite_shape_bit_envelope
        if type(extension_degree) is not int or extension_degree < 2:
            raise ValueError('finite extension degree >=2 required')
        ring = finite_shape_bit_envelope(extension_degree, self.max_center_precision)
        B = max(1, self.max_rational_bits, self.coefficients,
                self.max_center_precision)
        arithmetic = (self.rational_multiplies + self.rational_additions
                      + self.rational_powers * max(1, self.max_order.bit_length())
                      + self.binomial_calls * self.max_order
                      + self.normalize_pairs + self.coordinates)
        rational = 256 * (B + 1)**3 * arithmetic
        ring_calls = (self.ring_multiplies * ring.mul_bits
                      + self.ring_additions * ring.add_bits
                      + self.ring_negations * ring.neg_bits
                      + self.ring_powers * ring.pow_bits(self.max_order))
        # Slope conversions and final rational-to-Padic conversions use
        # modular odd-denominator inverses, polynomial by Euclid.
        conversions = self.normalize_pairs + self.coordinates
        ring_calls += conversions * 256 * (B + ring.canonical_payload_bits + 1)**3
        overhead = (2*self.L + self.center_scans + self.coefficients*self.coordinates
                    + self.binomial_calls + 20) * (B + ring.canonical_payload_bits + 1)**2
        return rational + ring_calls + overhead


def recovery_work(
    M: int, L: int, u: int, p: int, *, extension_degree: int,
    inherited_jet_lengths: Sequence[int] = (),
) -> RecoveryWork:
    """Count center classes by v2(t), matching StreamingHermite precisely.

    Assumes supplied jets have canonical values at the center precision.
    No center, coefficient or fraction is constructed in this function.
    """
    if any(type(v) is not int for v in (M, L, u, p, extension_degree)):
        raise ValueError('exact integers required')
    if (M < 0 or L < 2 or L & (L-1) or u < 1 or p < 1
            or extension_degree < 2 or any(type(q) is not int or q < 1
                                           for q in inherited_jet_lengths)):
        raise ValueError('invalid finite recovery schedule')
    a = L.bit_length() - 1
    h = (3*M + u - 1)//u
    # For i<a there are L/2**i centers; for i=a, only t=-L.
    classes = tuple((i, L>>i if i<a else 1, h*(u-i))
                    for i in range(min(a,u-1)+1) if h and u>i)
    C = sum(count for _,count,_ in classes)
    Q = sum(count*q for _,count,q in classes)
    qmax = max((q for _,_,q in classes), default=0)
    sq = sum(count*q*q for _,count,q in classes)
    prec = max((p+8*h*(L>>i)+8*M*(a+1) for i,_,_ in classes),default=p)
    pairs = C*max(C-1,0)
    binoms = max(C-1,0)*Q
    unit_pairs = max(C-1,0)*sq
    rec_pairs = sum(count*q*(q-1)//2 for _,count,q in classes)
    quot_pairs = sum(count*q*(q+1)//2 for _,count,q in classes)
    # Each base factor -s/(t-s), and -t/(2L), has numerator and
    # denominator bounded by 2L in absolute value.
    H = 1 + (a+2)*max(Q-1,0)
    denom_bits = 1 + Q*H
    num_bits = 4 + prec + H + Q*H + Q.bit_length()
    D = extension_degree*prod(inherited_jet_lengths)
    live_center = qmax*D*prec
    return RecoveryWork(
        M=M,L=L,u=u,p=p,coordinates=D,centers=C,coefficients=Q,
        max_order=qmax,max_center_precision=prec,
        normalize_pairs=pairs,center_scans=C*(2*L-1),
        binomial_calls=binoms,unit_convolution_pairs=unit_pairs,
        reciprocal_pairs=rec_pairs,quotient_pairs=quot_pairs,
        ring_powers=binoms,
        ring_multiplies=binoms+unit_pairs+rec_pairs+quot_pairs,
        ring_additions=unit_pairs+rec_pairs+quot_pairs,
        ring_negations=sum(count*(q-1) for _,count,q in classes),
        rational_powers=pairs+Q,
        rational_multiplies=pairs+Q+Q*D,
        rational_additions=Q*D,
        max_scale_bits=H,max_answer_numerator_bits=num_bits,
        max_answer_denominator_bits=denom_bits,
        center_payload_bits=live_center,
        eager_input_payload_bits=Q*D*prec,
        retained_abstract_payload_bits=(10*live_center+D*(num_bits+denom_bits)
                                        +(2*L-1)*(a+qmax.bit_length()+3)
                                        +qmax+4*H),
    )
