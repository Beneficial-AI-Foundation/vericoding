// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): original helper is fine, no changes needed */
fn min(a: i32, b: i32) -> i32 { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> result <= a[i],
        exists|i: int| 0 <= i < a.len() && result == a[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed loop invariant to reflect min_val correctly based on processed elements */
{
    let mut min_val = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> min_val <= a[k],
            exists|k: int| 0 <= k < i && min_val == a[k],
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
        }
        i = i + 1;
    }
    min_val
}
// </vc-code>

}
fn main() {}