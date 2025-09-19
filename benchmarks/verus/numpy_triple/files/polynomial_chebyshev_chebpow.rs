// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn chebpow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        pow <= maxpower,
    ensures
        /* Special case: pow = 0 returns [1.0] */
        (pow == 0) ==> (result.len() == 1 && result[0] == 1.0),
        /* Special case: pow = 1 returns input unchanged */
        (pow == 1) ==> (result.len() == c.len() && 
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
        /* Result length is correct */
        result.len() == (if pow == 0 { 1 } else { 1 + (c.len() - 1) * (pow as usize) }),
        /* For pow > 1: first coefficient exists when appropriate */
        (pow > 1 && c.len() >= 1) ==> (result.len() > 0),
        /* Non-triviality for pow >= 2 with sufficient input length */
        (pow >= 2 && c.len() >= 2 && result.len() > 2) ==> 
            (result[0] != 0.0 || result[1] != 0.0 || result[2] != 0.0),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}