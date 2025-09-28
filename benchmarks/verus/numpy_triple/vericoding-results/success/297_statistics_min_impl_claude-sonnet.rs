// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        exists|i: int| 0 <= i < a@.len() && a@[i] == result as int,
        forall|i: int| 0 <= i < a@.len() ==> result as int <= a@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed initial loop invariant by ensuring exists condition holds before loop */
    let mut min_val = a[0];
    let mut idx = 1;
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            exists|i: int| 0 <= i < idx && a@[i] == min_val as int,
            forall|i: int| 0 <= i < idx ==> min_val as int <= a@[i],
        decreases a.len() - idx
    {
        if a[idx] < min_val {
            min_val = a[idx];
        }
        idx += 1;
    }
    min_val
}
// </vc-code>


}
fn main() {}