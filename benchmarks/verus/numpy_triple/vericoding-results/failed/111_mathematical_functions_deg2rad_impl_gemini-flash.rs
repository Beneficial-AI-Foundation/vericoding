// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed; not needed. */
// </vc-helpers>

// <vc-spec>
fn deg2rad(degrees: Vec<i8>) -> (radians: Vec<i8>)
    ensures 
        radians.len() == degrees.len(),
        forall|i: int| 0 <= i < degrees.len() ==> #[trigger] radians@[i] as int == degrees@[i] as int * 314 / 18000
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added curly braces around `invariant auto`. */
{
    let mut radians: Vec<i8> = Vec::new();
    let mut i: nat = 0;
    while i < degrees.len()
        invariant auto {
            i <= degrees.len(),
            radians.len() == i,
            // degrees.len() == old(degrees.len()), // old() on mutable reference, not needed here
            forall|j: int| 0 <= j < i ==> #[trigger] radians@[j] as int == degrees@[j] as int * 314 / 18000,
        }
        decreases degrees.len() - i
    {
        radians.push(((degrees.view_at(i as int) as i32 * 314) / 18000) as i8);
        i = i + 1;
    }
    radians
}
// </vc-code>


}
fn main() {}