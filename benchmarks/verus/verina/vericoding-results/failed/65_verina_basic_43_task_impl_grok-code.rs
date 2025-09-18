// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed */
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use ghost variables for integer calculations to avoid type errors in exec code */
    ghost let n_int: int = n;
    ghost let two_n: int = 2 * n_int;
    ghost let two_n_plus_1: int = two_n + 1;
    ghost let n2: int = n_int * n_int;
    ghost let n3: int = n2 * n_int;
    ghost let twentyfour_n3: int = 24 * n3;
    ghost let twelve_n2: int = 12 * n2;
    ghost let fourteen_n: int = 14 * n_int;
    ghost let inside: int = 7 + twentyfour_n3 - twelve_n2 - fourteen_n;
    ghost let numerator: int = n_int * two_n_plus_1 * inside;
    proof {
        assert(numerator % 15 == 0) by (nonlinear_arith);
        assert(numerator / 15 >= 0);
    };
    let result: nat = (numerator / 15) as nat;
    result
}
// </vc-code>

}
fn main() {}