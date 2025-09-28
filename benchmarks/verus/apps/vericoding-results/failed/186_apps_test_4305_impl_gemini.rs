// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(h: int, a: int) -> bool {
    h >= 1 && a >= 1
}

spec fn is_minimum_attacks(attacks: int, h: int, a: int) -> bool {
    attacks >= 1 &&
    attacks * a >= h &&
    (attacks - 1) * a < h
}

spec fn ceil_div(h: int, a: int) -> int
    recommends a > 0
{
    (h + a - 1) / a
}
// </vc-preamble>

// <vc-helpers>
#[verifier(spinoff_prover)]
fn lemma_ceil_div_is_minimum(h: int, a: int)
    requires
        h >= 1,
        a >= 1,
    ensures
        is_minimum_attacks(ceil_div(h, a), h, a),
{
    let attacks = ceil_div(h, a);
    let num = h + a - 1;

    proof {
        if attacks == 0 {
            vstd::arithmetic::div_mod::lemma_div_is_zero(num, a);
            assert(num >= a);
            assert(false);
        }
    }
    vstd::arithmetic::div_mod::lemma_div_multiplied_by_divisor(num, a);
    vstd::arithmetic::div_mod::lemma_div_multiplied_by_divisor_is_le(num, a);
}
// </vc-helpers>

// <vc-spec>
fn solve(h: i8, a: i8) -> (attacks: i8)
    requires 
        valid_input(h as int, a as int)
    ensures 
        is_minimum_attacks(attacks as int, h as int, a as int),
        attacks as int == ceil_div(h as int, a as int)
// </vc-spec>
// <vc-code>
{
    let h_int = h as int;
    let a_int = a as int;

    let attacks_int = ceil_div(h_int, a_int);

    lemma_ceil_div_is_minimum(h_int, a_int);

    proof {
        if a_int > 1 {
            assert(h_int * a_int >= h_int + a_int - 1) by {
                assert((h_int - 1) * (a_int - 1) >= 0);
            };
            vstd::arithmetic::div_mod::lemma_div_le(h_int + a_int - 1, h_int, a_int);
        }
        assert(attacks_int <= h_int);
    }

    attacks_int as i8
}
// </vc-code>


}

fn main() {}