// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): returns the maximum of two i32 values */
fn max_i32(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)

    requires
        a.len() > 0,

    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate using usize indices and spec-level int indexing in invariants */
    let mut i: usize = 1;
    let mut max: i32 = a[0];
    while i < a.len()
        invariant
            0 <= (i as int),
            (i as int) <= (a.len() as int),
            forall|j: int| 0 <= j < (i as int) ==> a[j] <= max,
            exists|k: int| 0 <= k < (i as int) && a[k] == max,
        decreases a.len() - i
    {
        if a[i] > max {
            max = a[i];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

}
fn main() {}