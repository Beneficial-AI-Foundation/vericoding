// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a@.len() && result as int == a@[i],
        forall|i: int| 0 <= i < a@.len() ==> a@[i] <= result as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed initial invariant by starting loop from index 1 */
    let mut max_val = a[0];
    let mut idx = 1;
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            exists|i: int| 0 <= i < idx && max_val as int == a@[i],
            forall|i: int| 0 <= i < idx ==> a@[i] <= max_val as int,
        decreases a.len() - idx
    {
        if a[idx] > max_val {
            max_val = a[idx];
        }
        idx += 1;
    }
    max_val
}
// </vc-code>


}
fn main() {}