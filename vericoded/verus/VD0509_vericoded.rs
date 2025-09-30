// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max(a: &[i32]) -> (result: i32)
    requires a.len() > 0
    ensures forall|j: int| 0 <= j < a.len() ==> result >= a[j]
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i as int ==> max_val >= a@[k],
        decreases a.len() - i
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i = i + 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}