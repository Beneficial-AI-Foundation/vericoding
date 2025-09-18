// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
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
/* code modified by LLM (iteration 5): fixed invariant syntax by wrapping quantifier in braces */
{
    let n = a.len();
    let mut i = 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall|j: int| 0 <= j < i ==> {
            int_abs((a[j] - b[j]) as int) <= (atol + rtol * int_abs(b[j] as int)) as int
        }
    {
        let a_val = a[i] as int;
        let b_val = b[i] as int;
        let diff = a_val - b_val;
        let abs_diff = if diff >= 0 { diff } else { -diff };
        let abs_b = if b_val >= 0 { b_val } else { -b_val };
        let threshold = (atol as int) + (rtol as int) * abs_b;
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