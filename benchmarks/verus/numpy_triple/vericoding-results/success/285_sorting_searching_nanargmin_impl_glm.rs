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
    /* code modified by LLM (iteration 2): fixed type mismatches by casting result to int in invariants */
    let mut result = 0;
    let mut min_val = a[0];
    
    let mut i = 1;
    while i < a.len()
        invariant
            0 <= result < a.len(),
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> min_val <= a[j],
            forall|j: int| 0 <= j < (result as int) ==> a[j] > min_val,
            min_val == a[result as int],
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
            result = i;
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}