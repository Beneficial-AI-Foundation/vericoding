// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma syntax with exclamation mark */
lemma abs_nonnegative!(x: int)
    ensures
        int_abs(x) >= 0,
{
    if x < 0 {
        assert(int_abs(x) == -x);
        assert(-x >= 0);
    } else {
        assert(int_abs(x) == x);
        assert(x >= 0);
    }
}

spec fn spec_abs_diff(a: i8, b: i8) -> int
    ensures
        result == int_abs((a - b) as int),
{
    int_abs((a - b) as int)
}

spec fn is_close(a: i8, b: i8, rtol: i8, atol: i8) -> bool
    requires
        rtol >= 0,
        atol >= 0,
    ensures
        result == (int_abs((a - b) as int) <= atol as int + rtol as int * int_abs(b as int)),
{
    int_abs((a - b) as int) <= atol as int + rtol as int * int_abs(b as int)
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
/* code modified by LLM (iteration 5): Fixed verification with proper typing and assertions */
{
    let len = a.len();
    let mut i: usize = 0;
    let mut result: bool = true;
    
    while i < len
        invariant
            i <= len,
            result == (forall|j: int| 0 <= j < i ==> is_close(a@[j], b@[j], rtol, atol)),
    {
        let a_val = a[i];
        let b_val = b[i];
        let abs_diff = int_abs((a_val - b_val) as int);
        let tolerance = (atol as int) + (rtol as int) * int_abs(b_val as int);
        
        proof {
            assert(abs_diff == spec_abs_diff(a_val, b_val));
            assert(is_close(a_val, b_val, rtol, atol) == (abs_diff <= tolerance));
        }
        
        if abs_diff > tolerance {
            result = false;
            break;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}