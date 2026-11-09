"""Exact, nonexecuting parameter auditor for Appendix D of OpenAI's ETH preprint.

This models s=2**lambda without allocating s. The specification's constants are
r=64, epsilon=1/(128*1024), H=ceil(s/floor(sqrt(lambda))) and the
recursion-depth schedule u_d, a_d. In particular it does NOT synthesize a
huge tensor network, evaluate interpolation, or certify the paper's proof.

The verifier checks *sufficient* power-of-two bounds for every possible
active child M>H and the worst-case edge envelope M<=s/8**d (C=1).
These bounds are conservative and independent of any particular packing.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from math import isqrt
import argparse
import json

EPS_DENOM = 128 * 1024
GROUPS = 64


def log2_ceil(n: int) -> int:
    if n < 1:
        raise ValueError('positive integer expected')
    return (n - 1).bit_length()


def at_least_power_of_two(exp: int, value: int) -> bool:
    """2**exp >= value without creating 2**exp."""
    if exp < 0:
        return False
    return value.bit_length() <= exp or (value.bit_length() == exp + 1 and value == (1 << exp))


def power_ge_ceil(a: int, b: int, numerator: int, denominator: int) -> bool:
    """2**a >= 2**(b+ceil(numerator/denominator))."""
    return a >= b + (numerator + denominator - 1) // denominator


@dataclass(frozen=True)
class Level:
    depth: int
    u: int
    a: int
    L_log2: int
    Darr_log2: int
    M_envelope_log2: int
    H_lower_log2: int
    active_possible: bool
    paper_u_positive: bool
    packet_count_bound: bool
    group_degree_bound: bool
    packets_polynomial_size: bool
    enough_interpolation_points: bool
    u_large_enough_for_asymptotic_proof: bool
    precision_sharpening_sufficient: bool
    child_ratio_num: int
    child_ratio_den: int
    max_precision_log2_upper: int
    max_interpolation_entries_log2_upper: int
    max_mode_descriptors_log2_upper: int
    max_mode_storage_log2_upper: int
    jet_field_storage_log2_upper: int
    counted_storage_under_s_to_fourth: bool

    def all_checked(self) -> bool:
        return (
            self.active_possible and self.paper_u_positive
            and self.packet_count_bound and self.group_degree_bound
            and self.packets_polynomial_size and self.enough_interpolation_points
            and self.u_large_enough_for_asymptotic_proof
            and self.precision_sharpening_sufficient
            and self.counted_storage_under_s_to_fourth
        )


@dataclass(frozen=True)
class Schedule:
    lambda_bits: int
    r: int
    epsilon_denominator: int
    symbolic_s: str
    H_lower_log2: int
    H_upper_log2: int
    delta_lower_log2: int
    delta_upper_log2: int
    levels: tuple[Level, ...]
    terminal_depth: int
    stopping_reason: str
    all_active_obligations_pass: bool
    full_execution_performed: bool = False

    def report(self, full: bool = False) -> dict:
        data={
            'lambda':str(self.lambda_bits), 'symbolic_s':self.symbolic_s,
            'r':self.r,'epsilon_denominator':self.epsilon_denominator,
            'H_lower_log2':str(self.H_lower_log2),
            'H_upper_log2':str(self.H_upper_log2),
            'delta_lower_log2':str(self.delta_lower_log2),
            'delta_upper_log2':str(self.delta_upper_log2),
            'active_depths':len(self.levels),
            'terminal_depth':self.terminal_depth,
            'stopping_reason':self.stopping_reason,
            'all_active_obligations_pass':self.all_active_obligations_pass,
            'full_execution_performed':False,
            'space_scope':'interpolation jets, coefficients, mode-count envelopes only; not an independent whole-program polynomial-space proof',
            'interpretation': 'symbolic sufficient-condition audit, not an executed contraction or proof certification',
        }
        if full:
            data['levels'] = [dict(asdict(lev),u=str(lev.u),a=str(lev.a),
                                   M_envelope_log2=str(lev.M_envelope_log2),
                                   H_lower_log2=str(lev.H_lower_log2)) for lev in self.levels]
        else:
            data['level_summary']=[{'depth':lev.depth, 'u':str(lev.u),
                                    'a':str(lev.a),
                                    'all_checked':lev.all_checked(),
                                    'precision_sharpening':lev.precision_sharpening_sufficient,
                                    'counted_storage_under_s_to_fourth':lev.counted_storage_under_s_to_fourth}
                                   for lev in self.levels[:4]]
            if len(self.levels)>4:
                data['last_level']={'depth':self.levels[-1].depth,
                                    'all_checked':self.levels[-1].all_checked()}
        return data


def audit_power_of_two(lambda_bits: int, *, max_depth: int = 10000) -> Schedule:
    """Audit the paper's true 64-group schedule on a symbolic s=2**lambda.

    M_envelope(d) = s/8**d. H is bounded by powers of two from below
    and above; if lambda is a square power of two, H is exact.
    Delta=ceil(s**(9/10)) is bounded by 2**floor(9 lambda/10)
    and 2**ceil(9 lambda/10).
    At every active depth, we demand packing conditions at *minimum*
    possible M>H, not merely at the largest possible M.
    """
    if lambda_bits < 2:raise ValueError('lambda must be at least 2')
    if max_depth < 1:raise ValueError('max_depth must be positive')
    Q=isqrt(lambda_bits)
    # floor(sqrt(lambda)) <= 2**ceil(log2(Q)); so H>=2**(lambda-ceil(log2 Q)).
    h_lower=lambda_bits-log2_ceil(Q)
    # Q >= 2**floor(log2 Q), so H <=2**(lambda-floor(log2 Q))+1.
    h_upper=lambda_bits-(Q.bit_length()-1)+1
    delta_low=(9*lambda_bits)//10
    delta_high=(9*lambda_bits+9)//10
    levels=[]
    a=0
    reason='max_depth_exceeded'
    for d in range(max_depth):
        # With s=2**lambda and M<=s/8**d, active possible iff
        # Mmax>H. Comparing Q with 8**d is exact for all relevant depths.
        if Q <= (1 << (3*d)):
            reason='maximum_child_edge_count_at_or_below_leaf_H'
            break
        u=lambda_bits//(EPS_DENOM*(1<<d))
        if u==0:
            reason='u_d_zero_before_leaf: finite-size exception required'
            break
        a+=2*u
        # M_min>H implies M_min>=2**h_lower. This yields conservative
        # sufficient conditions using Delta <=2**delta_high.
        packet_count_bound = (h_lower >= 1+24*a+delta_high and
                              h_lower >= 13*a)
        group_degree_bound = (a+1 <= delta_low)
        packets_polynomial_size = (1000*a <= lambda_bits and
                                   12000*a <= lambda_bits and
                                   32768*a <= lambda_bits)
        envelope=lambda_bits-3*d
        # Degree <= M*(2L-1); degree+1 <=2ML.
        enough_interpolation_points = (envelope+a+1 <=4*lambda_bits)
        # Paper requires u>=lambda**(4/5) for its uniform sharpened bound.
        u_large = u**5>=lambda_bits**4
        # Input precision at depth d is at most
        # s*2**(a_prev+6+ceil(log2(d+1))) for P0<=s,
        # since each earlier increment <= s*2**(a_j+6)/8**j.
        # Require conservatively p_input<=32 M_min D_min/u and
        # 8M(a+1)<=8 M D_min/u. Together with 8hD<=32MD/u,
        # this implies p_t <=72 M D/u for every active t.
        a_prev=a-2*u
        pinput_upper=lambda_bits+a_prev+6+log2_ceil(d+1)
        dmin_log2=a-u+1  # i=u-1, D=L/2**i
        pt_input_ok = (pinput_upper+log2_ceil(u)
                       <=5+h_lower+dmin_log2)
        # D_min>=u(a+1), checked by integer bit lengths.
        pt_eval_ok = at_least_power_of_two(dmin_log2,u*(a+1))
        # Conservative counted-structure envelopes, not a bound on all
        # Python object overhead or on arbitrary user-provided oracles:
        # p_t <=72 M D/u <=128 M L, number of interpolation coefficients
        # <=2ML, number of jets <=8ML, and modes <=6M*p_t.
        # A field coefficient occupies <=e*p_t bits; jet storage is at
        # most 8ML*e*p_t bits. e=4lambda. These are polynomial in s.
        pmax_exp=envelope+a+7
        interp_exp=envelope+a+1
        modes_exp=2*envelope+a+10
        # Current Mode.tile can list up to L edges, each with an
        # O(log s) identifier, rather than a constant-sized record.
        modes_storage_exp=modes_exp+a+log2_ceil(lambda_bits)+10
        jets_field_exp=2*envelope+2*a+10+log2_ceil(4*lambda_bits)
        storage_s4=max(modes_storage_exp, jets_field_exp)<4*lambda_bits
        levels.append(Level(
            depth=d,u=u,a=a,L_log2=a,Darr_log2=12*a,
            M_envelope_log2=envelope,H_lower_log2=h_lower,
            active_possible=True,paper_u_positive=True,
            packet_count_bound=packet_count_bound,
            group_degree_bound=group_degree_bound,
            packets_polynomial_size=packets_polynomial_size,
            enough_interpolation_points=enough_interpolation_points,
            u_large_enough_for_asymptotic_proof=u_large,
            precision_sharpening_sufficient=pt_input_ok and pt_eval_ok,
            child_ratio_num=3,child_ratio_den=32,
            max_precision_log2_upper=pmax_exp,
            max_interpolation_entries_log2_upper=interp_exp,
            max_mode_descriptors_log2_upper=modes_exp,
            max_mode_storage_log2_upper=modes_storage_exp,
            jet_field_storage_log2_upper=jets_field_exp,
            counted_storage_under_s_to_fourth=storage_s4,
        ))
    else:
        d=max_depth
    return Schedule(lambda_bits, GROUPS, EPS_DENOM,
                    f'2^(lambda) with lambda={lambda_bits}',h_lower,h_upper,
                    delta_low,delta_high,tuple(levels),d,reason,
                    reason.startswith('maximum_') and bool(levels)
                    and all(lev.all_checked() for lev in levels))


def main():
    ap=argparse.ArgumentParser(description='Symbolic Appendix D parameter audit, NOT a contraction run')
    group=ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--lambda-bits',type=int,
                       help='lambda=ceil(log2 s); study symbolic s=2**lambda')
    group.add_argument('--lambda-power',type=int,
                       help='study lambda=2**k and symbolic s=2**(2**k)')
    ap.add_argument('--full',action='store_true')
    ap.add_argument('--output',type=str)
    args=ap.parse_args()
    lam=args.lambda_bits if args.lambda_bits is not None else 1<<args.lambda_power
    doc=audit_power_of_two(lam).report(full=args.full)
    txt=json.dumps(doc,indent=2)
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(txt+'\n')
    print(txt)

if __name__=='__main__':main()
