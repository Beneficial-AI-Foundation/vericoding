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
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut max = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            0 < i <= a.len(),
            forall|k: int| 0 <= k < i ==> max >= a[k],
            exists|k: int| 0 <= k < i && max == a[k],
        decreases a.len() - i
    {
        if a[i] > max {
            max = a[i];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

}
fn main() {}