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
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut min = a[0];
    let mut min_index: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            i <= a.len(),
            0 <= min_index < a.len(),
            min == a[min_index as int],
            forall|j: int| 0 <= j < i ==> min <= a[j],
            exists|j: int| 0 <= j < i && min == a[j],
        decreases a.len() - i,
    {
        if a[i] < min {
            min = a[i];
            min_index = i;
        }
        i += 1;
    }
    min
}
// </vc-code>

}
fn main() {}