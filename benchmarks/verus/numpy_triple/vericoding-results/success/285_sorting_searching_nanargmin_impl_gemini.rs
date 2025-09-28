// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<i8>) -> (result: usize)
    requires 
        a.len() > 0,
    ensures
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a[result as int] <= a[j],
        forall|j: int| 0 <= j < result ==> a[j] > a[result as int],
// </vc-spec>
// <vc-code>
{
    let mut min_index: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            0 < i <= a.len(),
            0 <= min_index < i,
            forall|j: int| 0 <= j < i ==> a@[min_index as int] <= a@[j],
            forall|j: int| 0 <= j < min_index ==> a@[j] > a@[min_index as int],
        decreases a.len() - i
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    min_index
}
// </vc-code>


}
fn main() {}