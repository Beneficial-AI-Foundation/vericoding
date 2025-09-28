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
/* code modified by LLM (iteration 2): strengthened loop invariants to track min_value and ensure first occurrence */
{
    let mut min_index = 0;
    let mut min_value = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a@.len(),
            0 <= min_index < i,
            min_value == a@[min_index as int],
            forall|k: int| 0 <= k < (i as int) ==> a@[min_index as int] <= a@[k],
            forall|k: int| 0 <= k < (min_index as int) ==> a@[k] > a@[min_index as int],
        decreases a.len() - i,
    {
        if a[i] < min_value {
            min_value = a[i];
            min_index = i;
        }
        i += 1;
    }
    min_index
}
// </vc-code>


}
fn main() {}