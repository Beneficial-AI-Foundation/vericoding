// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): Removed ghost type usage in runtime code by using direct Vec indexing and casting to i32 for computations to prevent overflow and type errors. */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            forall|j: int| 0 <= j < i ==> int_abs((a@[j] - b@[j]) as int) <= (atol as int + rtol as int * int_abs(b@[j] as int)),
        decreases a@.len() - i
    {
        let a_val = a[i] as i32;
        let b_val = b[i] as i32;
        let diff = a_val - b_val;
        let abs_diff = if diff < 0 { -diff } else { diff };
        let abs_b = if b_val < 0 { -b_val } else { b_val };
        let rtol_term = (rtol as i32) * abs_b;
        let threshold = (atol as i32) + rtol_term;
        if abs_diff > threshold {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}