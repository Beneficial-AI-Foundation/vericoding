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
    /* code modified by LLM (iteration 2): fixed int type usage in exec code */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            rtol >= 0,
            atol >= 0,
            forall|j: int| 0 <= j < i ==> int_abs((a[j] - b[j]) as int) <= (atol as int + rtol as int * int_abs(b[j] as int)),
    {
        let diff_i8 = a[i] - b[i];
        let abs_diff = if diff_i8 >= 0 { diff_i8 } else { -diff_i8 };
        let abs_b = if b[i] >= 0 { b[i] } else { -b[i] };
        let threshold = atol + rtol * abs_b;
        
        if abs_diff > threshold {
            assert(int_abs((a[i] - b[i]) as int) > (atol as int + rtol as int * int_abs(b[i] as int)));
            return false;
        }
        assert(int_abs((a[i] - b[i]) as int) <= (atol as int + rtol as int * int_abs(b[i] as int)));
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}