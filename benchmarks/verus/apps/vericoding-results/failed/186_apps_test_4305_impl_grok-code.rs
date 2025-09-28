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
    /* code modified by LLM (iteration 5): Added proof block to assert postconditions for ceiling division and minimum attacks, ensuring verification of ensures clauses */
    let h_i32: i32 = h as i32;
    let a_i32: i32 = a as i32;
    let q: i32 = h_i32 / a_i32;
    let r: i32 = h_i32 % a_i32;
    let attacks_val = if r == 0 { q } else { q + 1 };
    proof {
        let h_int: int = h as int;
        let a_int: int = a as int;
        // Prove the computed attacks_val matches ceil_div
        if r == 0 {
            assert(attacks_val as int == q as int);
            assert(q as int == h_int / a_int);
            assert(h_int % a_int == 0);
        } else {
            assert(attacks_val as int == q as int + 1);
            assert(q as int == h_int / a_int);
            assert(h_int % a_int == r as int && r > 0);
            assert(attacks_val as int == h_int / a_int + 1);
        }
        assert(attacks_val as int == ceil_div(h_int, a_int));
        // Prove is_minimum_attacks
        assert(attacks_val as int >= 1);
        assert((attacks_val as int) * a_int >= h_int);
        assert(((attacks_val as int) - 1) as int * a_int < h_int);
        assert(is_minimum_attacks(attacks_val as int, h_int, a_int));
    }
    #[verifier::truncate] attacks_val as i8
}
// </vc-code>


}

fn main() {}