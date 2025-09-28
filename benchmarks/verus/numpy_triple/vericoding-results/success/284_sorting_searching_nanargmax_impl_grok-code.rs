// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nanargmax(a: Vec<i8>) -> (idx: usize)
    requires 
        a@.len() > 0,
    ensures 
        idx < a@.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[j] <= a@[idx as int],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[idx as int] ==> (idx as int) <= j,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): added decreases clause to the while loop to fix verification error */
    let mut idx: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            idx < i,
            forall|k: int| 0 <= k < i ==> a@[k] <= a@[idx as int],
            forall|k: int| 0 <= k < i && a@[k] == a@[idx as int] ==> idx <= k,
        decreases a.len() - i
    {
        if a[i] > a[idx] {
            idx = i;
        }
        i = i + 1;
    }
    idx
}
// </vc-code>


}
fn main() {}