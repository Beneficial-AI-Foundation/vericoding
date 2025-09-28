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
{
    /* code modified by LLM (iteration 5): add detailed proof about calculation correctness */
    // The specification is impossible, as the result (up to 200) cannot fit in an i8.
    // This implementation correctly calculates the value and proves its correspondence
    // to the spec. The inevitable verification failure on the return statement
    // correctly identifies the contradiction in the function's contract.

    let pies_calc = ((a as i16) * 3 + (p as i16)) / 2;

    proof {
        let a_int = a as int;
        let p_int = p as int;
        let spec_val = max_pies(a_int, p_int);

        assert(pies_calc as int == spec_val) by {
            let spec_total = total_pieces(a_int, p_int);
            let exec_total = (a as i16) * 3 + (p as i16);

            assert(exec_total as int == spec_total) by {
                // i16 is large enough to prevent overflow for intermediate computations.
                // Max value of a*3 + p is 100*3 + 100 = 400, which fits in i16.
            };

            // For non-negative values, truncating division (for i16) and
            // Euclidean division (for int) are equivalent.
            assert(exec_total >= 0);
            vstd::arithmetic::div_mod::lemma_div_is_for_nonneg(exec_total as int, 2);
            assert((exec_total / 2) as int == (exec_total as int) / 2);
        };
    }

    pies_calc as i8
}
// </vc-code>


}

fn main() {}