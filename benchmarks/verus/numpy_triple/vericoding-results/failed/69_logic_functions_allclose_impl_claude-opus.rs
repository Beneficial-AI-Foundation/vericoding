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
    /* code modified by LLM (iteration 5): Use manual negation instead of saturating_neg */
    if a.len() != b.len() {
        return false;
    }
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> int_abs((a[j] - b[j]) as int) <= (atol + rtol * int_abs(b[j] as int)) as int,
        decreases a.len() - i,
    {
        let diff = a[i] - b[i];
        let abs_diff = if diff >= 0 { diff } else { -diff };
        let abs_b = if b[i] >= 0 { b[i] } else { -b[i] };
        let threshold = atol + rtol * abs_b;
        
        if abs_diff > threshold {
            return false;
        }
        
        assert(int_abs((a[i] - b[i]) as int) == abs_diff as int);
        assert(int_abs(b[i] as int) == abs_b as int);
        assert(abs_diff as int <= threshold as int);
        
        i = i + 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}