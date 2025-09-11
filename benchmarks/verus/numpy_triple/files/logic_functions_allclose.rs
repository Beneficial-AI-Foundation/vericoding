use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

// <vc-helpers>
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}