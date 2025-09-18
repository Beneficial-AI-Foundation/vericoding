// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed, no helpers needed */
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
/* code modified by LLM (iteration 5): fixed compilation errors by using direct array indexing/casting and `usize` type for loop variable */
{
    let len_a = a.len();
    let len_b = b.len();

    let mut i: usize = 0;
    while i < len_a
        invariant 
            0 <= i as int,
            i as int <= len_a as int,
            
            forall|j: int| 0 <= j < i ==> 
                int_abs(a[j as usize] as int - b[j as usize] as int) <= (atol as int + rtol as int * int_abs(b[j as usize] as int))
    {
        let diff_val = (a[i] - b[i]) as int;
        let b_val_abs = int_abs(b[i] as int);
        let bound_val = atol as int + rtol as int * b_val_abs;

        if int_abs(diff_val) > bound_val {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}