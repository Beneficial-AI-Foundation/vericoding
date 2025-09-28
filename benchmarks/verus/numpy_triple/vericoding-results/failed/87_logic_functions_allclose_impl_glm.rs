// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix trigger syntax by using proper Verus syntax */
spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-helpers>

// <vc-spec>
fn allclose(a: Vec<i8>, b: Vec<i8>, rtol: i8, atol: i8) -> (result: bool)
    requires 
        a.len() == b.len(),
        rtol >= 0,
        atol >= 0,
    ensures 
        result == (forall|i: int| 0 <= i < a@.len() ==> 
            int_abs((a[i] - b[i]) as int) <= (atol as int + rtol as int * int_abs(b[i] as int)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix trigger syntax by removing square brackets */
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            forall|j: int| 0 <= j < i ==> 
                int_abs((a[j] - b[j]) as int) <= (atol as int + rtol as int * int_abs(b[j] as int)),
        decreases a@.len() - i
    {
        let a_i = a[i] as i32;
        let b_i = b[i] as i32;
        let diff = a_i - b_i;
        let abs_diff = if diff >= 0 { diff } else { -diff };
        let atol_i32 = atol as i32;
        let rtol_i32 = rtol as i32;
        let abs_b_i = if b_i >= 0 { b_i } else { -b_i };
        let tolerance = atol_i32 + rtol_i32 * abs_b_i;

        if abs_diff > tolerance {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}