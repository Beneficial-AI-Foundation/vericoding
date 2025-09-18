// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. Retained for verifiable absolute value computation. */
fn i64_abs(x: i64) -> (res: i64)
    ensures res == int_abs(x as int)
{
    if x < 0 { -x } else { x }
}

/* helper modified by LLM (iteration 5): No changes needed. Retained for loop invariant. */
spec fn allclose_item(a_val: i32, b_val: i32, rtol: i32, atol: i32) -> bool { int_abs((a_val - b_val) as int) <= (atol as int + (rtol as int) * int_abs(b_val as int)) }
// </vc-helpers>

// <vc-spec>
fn allclose(a: Vec<i32>, b: Vec<i32>, rtol: i32, atol: i32) -> (result: bool)
    requires 
        a.len() == b.len(),
        rtol >= 0,
        atol >= 0,
    ensures 
        result == (forall|i: int| 0 <= i < a.len() ==> 
            int_abs((a[i] - b[i]) as int) <= (atol + rtol * int_abs(b[i] as int)) as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added a decreases clause to the while loop to prove termination. */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            rtol >= 0,
            atol >= 0,
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> allclose_item(a@[j], b@[j], rtol, atol)
        decreases a.len() - i
    {
        let a_val = a[i];
        let b_val = b[i];

        let a_i64 = a_val as i64;
        let b_i64 = b_val as i64;
        let rtol_i64 = rtol as i64;
        let atol_i64 = atol as i64;

        let threshold = atol_i64 + rtol_i64 * i64_abs(b_i64);
        let abs_diff = i64_abs(a_i64 - b_i64);
        
        if abs_diff > threshold {
            return false;
        }
        
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}