// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed to use i64 to avoid overflow in calculations */
fn abs_i64(x: i64) -> (res: i64)
    requires
        x > i64::MIN,
    ensures 
        res >= 0,
        res as int == int_abs(x as int),
{
    if x < 0 { -x } else { x }
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
{
    /* code modified by LLM (iteration 4): changed intermediate calculations to use i64 to avoid potential overflow */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            rtol >= 0,
            atol >= 0,
            forall|j: int| 0 <= j < i@ ==> 
                int_abs((a@[j] as int - b@[j] as int)) <= (atol as int + rtol as int * int_abs(b@[j] as int)),
        decreases a.len() - i
    {
        let a_i = a[i] as i64;
        let b_i = b[i] as i64;
        let rtol_i64 = rtol as i64;
        let atol_i64 = atol as i64;

        let diff = a_i - b_i;
        assert(diff > i64::MIN);
        let abs_diff = abs_i64(diff);

        assert(b_i > i64::MIN);
        let b_i_abs = abs_i64(b_i);
        
        let tolerance = atol_i64 + rtol_i64 * b_i_abs;

        if abs_diff > tolerance {
            return false;
        }
        
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}