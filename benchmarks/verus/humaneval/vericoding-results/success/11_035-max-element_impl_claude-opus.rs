// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)

    requires
        a.len() > 0,

    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut max = a[0];
    let mut j: usize = 1;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            forall|i: int| 0 <= i < j ==> a[i] <= max,
            exists|i: int| 0 <= i < j && a[i] == max,
        decreases a.len() - j
    {
        if a[j] > max {
            max = a[j];
        }
        j = j + 1;
    }
    max
}
// </vc-code>

}
fn main() {}