// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added safe absolute value function with overflow checks */
fn exec_abs(x: i32) -> (result: i32)
    requires x > i32::MIN
    ensures result as int == int_abs(x as int)
{
    if x >= 0 { x } else { -x }
}

/* helper modified by LLM (iteration 5): added safe subtraction with overflow checks */
fn safe_sub(a: i32, b: i32) -> (result: i32)
    requires a as int - b as int <= i32::MAX as int && a as int - b as int >= i32::MIN as int
    ensures result as int == a as int - b as int
{
    a - b
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
    /* code modified by LLM (iteration 5): fixed syntax error in overflow check */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> int_abs((a@[j] - b@[j]) as int) <= (atol + rtol * int_abs(b@[j] as int)) as int
        decreases a.len() - i
    {
        if a[i] as int - b[i] as int > i32::MAX as int || a[i] as int - b[i] as int < (i32::MIN as int) {
            return false;
        }
        if b[i] == i32::MIN {
            return false;
        }
        let diff_val = safe_sub(a[i], b[i]);
        let diff = exec_abs(diff_val);
        let b_abs = exec_abs(b[i]);
        let tolerance = atol + rtol * b_abs;
        if diff > tolerance {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}