// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> result <= a[i],
        exists|i: int| 0 <= i < a.len() && result == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added a decreases clause to the while loop to prove termination. */
    let mut min = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            a.len() > 0,
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < (i as int) ==> min <= a[j],
            exists|j: int| 0 <= j < (i as int) && min == a[j],
        decreases a.len() - i
    {
        if a[i] < min {
            min = a[i];
        }
        i = i + 1;
    }
    min
}
// </vc-code>

}
fn main() {}