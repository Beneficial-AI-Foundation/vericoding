// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
spec fn is_close(a: i32, b: i32, rtol: i32, atol: i32) -> bool {
    let diff: int = (a as int) - (b as int);
    let abs_diff: int = if diff < 0 { -diff } else { diff };
    let abs_b: int = if b < 0 { -(b as int) } else { b as int };
    abs_diff <= (atol as int) + (rtol as int) * abs_b
}
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
/* code modified by LLM (iteration 5): Fixed compilation errors by using i64 for arithmetic calculations instead of int in exec code */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i as int <= a.len() as int,
            forall |j: int| 0 <= j < i ==> is_close(a@[j], b@[j], rtol, atol)
    {
        let a_val = a[i];
        let b_val = b[i];
        let diff_i64: i64 = a_val as i64 - b_val as i64;
        let abs_diff: i64 = if diff_i64 < 0 { -diff_i64 } else { diff_i64 };
        let abs_b: i64 = if b_val < 0 { -(b_val as i64) } else { b_val as i64 };
        if abs_diff > (atol as i64) + (rtol as i64) * abs_b {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}