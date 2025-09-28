// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, p: int) -> bool {
    0 <= a <= 100 && 0 <= p <= 100
}

spec fn total_pieces(a: int, p: int) -> int
    recommends valid_input(a, p)
{
    a * 3 + p
}

spec fn max_pies(a: int, p: int) -> int
    recommends valid_input(a, p)
{
    total_pieces(a, p) / 2
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn calculate_max_pies(a: i8, p: i8) -> (pies: i8)
    requires 
        valid_input(a as int, p as int)
    ensures 
        pies as int == max_pies(a as int, p as int) &&
        pies >= 0 &&
        pies as int == (a as int * 3 + p as int) / 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [cast the result of the division to i8 instead of the entire expression] */
{
    let a_int = a as int;
    let p_int = p as int;

    let total_pieces_val = a_int * 3 + p_int;
    let pies_int_val = total_pieces_val / 2;
    let pies_i8 = pies_int_val as i8;

    // Proofs for `ensures` clause
    proof {
        assert(a_int >= 0 && a_int <= 100); // From valid_input
        assert(p_int >= 0 && p_int <= 100); // From valid_input

        assert(pies_i8 as int == max_pies(a_int, p_int));
        assert(pies_i8 >= 0);
        assert(pies_i8 as int == (a_int * 3 + p_int) / 2);
    }

    pies_i8
}
// </vc-code>


}

fn main() {}