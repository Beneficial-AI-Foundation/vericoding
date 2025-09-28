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
    let mut min_val = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> min_val <= a[j],
            exists|j: int| 0 <= j < i && min_val == a[j],
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
        }
        i += 1;
    }
    min_val
}
// </vc-code>

}
fn main() {}