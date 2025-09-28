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
    /* code modified by LLM (iteration 5): added decreases clause to fix compilation error */
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            rtol >= 0,
            atol >= 0,
            forall|j: int| 0 <= j < i ==> int_abs((a@[j] - b@[j]) as int) <= (atol as int + rtol as int * int_abs(b@[j] as int)),
        decreases a.len() - i
    {
        let a_val = a[i];
        let b_val = b[i];
        let diff_val = if a_val >= b_val { a_val - b_val } else { b_val - a_val };
        let b_abs = if b_val >= 0 { b_val } else { -b_val };
        let tolerance_val = atol + rtol * b_abs;
        
        proof {
            let diff_int = int_abs((a@[i as int] - b@[i as int]) as int);
            let tolerance_int = atol as int + rtol as int * int_abs(b@[i as int] as int);
            assert(diff_val as int == diff_int);
            assert(tolerance_val as int == tolerance_int);
        }
        
        if diff_val > tolerance_val {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}