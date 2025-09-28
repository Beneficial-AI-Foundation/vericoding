// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_argmin(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[result as int] <= a@[j],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[result as int] ==> (result as int) <= j,
// </vc-spec>
// <vc-code>
{
    let mut min_idx: usize = 0;
    let mut min_val: i8 = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= min_idx < a.len(),
            min_idx < i <= a.len(),
            min_val == a@[min_idx as int],
            forall|j: int| 0 <= j < i ==> a@[min_idx as int] <= a@[j],
            forall|j: int| 0 <= j < i && a@[j] == a@[min_idx as int] ==> (min_idx as int) <= j,
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
            min_idx = i;
        }
        i = i + 1;
    }
    
    min_idx
}
// </vc-code>


}
fn main() {}