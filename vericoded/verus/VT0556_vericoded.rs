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
    let mut argmax_idx: usize = 0;
    let mut max_val = a[0];
    let mut i: usize = 1;

    while i < a.len()
        invariant
            1 <= i <= a.len(),
            0 <= argmax_idx < i,
            max_val == a@[argmax_idx as int],
            forall|k: int| 0 <= k < i ==> a@[k] <= max_val,
            forall|k: int| 0 <= k < i && a@[k] == max_val ==> argmax_idx <= k as usize,
        decreases a.len() - i
    {
        if a[i] > max_val {
            max_val = a[i];
            argmax_idx = i;
        }
        i = i + 1;
    }
    
    argmax_idx
}
// </vc-code>

}
fn main() {}