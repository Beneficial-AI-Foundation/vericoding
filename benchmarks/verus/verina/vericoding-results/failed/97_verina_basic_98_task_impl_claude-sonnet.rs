// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use integer division without exec mode operations */
spec fn is_multiple_of_three(x: i32) -> bool { x % 3 == 0 }

proof fn triple_division_proof(x: i32)
    requires x > -715827882 && x < 715827882
    ensures (x * 3) / 3 == x
{
}

proof fn triple_mod_proof(x: i32)
    requires x > -715827882 && x < 715827882
    ensures (x * 3) % 3 == 0
{
}

proof fn division_multiplication_proof(x: i32)
    requires x > -715827882 && x < 715827882
    ensures (x * 3) / 3 * 3 == x * 3
{
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): remove misplaced requires clause from function body */
{
    let result = x * 3;
    proof {
        triple_division_proof(x);
        triple_mod_proof(x);
        division_multiplication_proof(x);
    }
    result
}
// </vc-code>

}
fn main() {}