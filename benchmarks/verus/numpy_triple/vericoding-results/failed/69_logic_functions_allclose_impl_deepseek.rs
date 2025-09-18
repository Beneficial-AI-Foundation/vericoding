// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed vector access preconditions and added helper for indexing */
proof fn lemma_vec_index_valid(i: usize, v: Vec<i32>)
    requires 0 <= i < v.len()
    ensures v@.index(i) == v[i]
{
}

spec fn abs_diff(a: i32, b: i32) -> int {
    let x = a as int;
    let y = b as int;
    if x >= y { x - y } else { y - x }
}

spec fn calc_threshold(b_val: i32, rtol: i32, atol: i32) -> int {
    (atol as int) + (rtol as int) * int_abs(b_val as int)
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
/* code modified by LLM (iteration 5): Added proper vector bounds checking and lemma calls */
{
    let n = a.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            forall|j: int| 0 <= j < i ==> {
                requires 0 <= j < n,
                int_abs((a[j] - b[j]) as int) <= (atol as int + (rtol as int) * int_abs(b[j] as int))
            }
        decreases n - i
    {
        proof {
            lemma_vec_index_valid(i, a.clone());
            lemma_vec_index_valid(i, b.clone());
        }
        
        let abs_diff_val = abs_diff(a[i], b[i]);
        let threshold_val = calc_threshold(b[i], rtol, atol);
        
        if (abs_diff_val as i32) > (threshold_val as i32) {
            return false;
        }
        
        i = i + 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}