// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argmax(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[j] <= a@[result as int],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[result as int] ==> result <= j as usize,
// </vc-spec>
// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;

    while i < a.len()
        invariant
            0 < a.len(),
            1 <= i,
            i <= a.len(),
            max_idx < i,
            max_idx < a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] <= a@[max_idx as int],
            forall|j: int| 0 <= j < i && a@[j] == a@[max_idx as int] ==> max_idx <= j as usize,
        decreases a.len() - i
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

}
fn main() {}