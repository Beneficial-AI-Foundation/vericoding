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
/* code modified by LLM (iteration 4): Fix Verus type errors by casting vector elements to `i8` before using them in arithmetic operations, as `i8` is a concrete type and `nat`/`int` are ghost. */
{
    let mut i: nat = 0;
    let len = a.len();

    while i < len
        invariant
            0 <= i <= len,
            a.len() == b.len(),
            rtol >= 0,
            atol >= 0,
            forall|j: int| 0 <= j < i ==> int_abs((a[j] - b[j]) as int) <= (atol as int + rtol as int * int_abs(b[j] as int))
    {
        let diff_val: i8 = a.view_at(i) - b.view_at(i);
        let b_val: i8 = b.view_at(i);

        if int_abs(diff_val as int) > (atol as int + rtol as int * int_abs(b_val as int)) {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}