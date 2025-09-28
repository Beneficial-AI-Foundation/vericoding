// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_array_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_array(a: &Vec<i32>) -> (result: i32)
    requires max_array_precond(a),
    ensures
        forall|k: int| 0 <= k < a.len() ==> result >= a[k],
        exists|k: int| 0 <= k < a.len() && result == a[k],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed compilation error by using usize for array indexing. */
    let mut max = a[0];
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 <= (max_idx as int) < (i as int),
            max == a[max_idx as int],
            forall|k: int| 0 <= k < i ==> max >= a[k],
        decreases a.len() - i,
    {
        if a[i] > max {
            max = a[i];
            max_idx = i;
        }
        i = i + 1;
    }
    max
}
// </vc-code>

}
fn main() {}