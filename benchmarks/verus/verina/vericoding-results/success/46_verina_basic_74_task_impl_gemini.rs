// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_array_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}
// </vc-preamble>

// <vc-helpers>
spec fn max(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}
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
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    let mut max = a[0];
    let mut i: usize = 1;

    while i < a.len()
        invariant
            1 <= i <= a.len(),
            exists|k: int| 0 <= k < i as int && max == a[k],
            forall|k: int| 0 <= k < i as int ==> max >= a[k],
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