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
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut min_val = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            exists|j: int| 0 <= j < i && a@[j] == min_val as int,
            forall|j: int| 0 <= j < i ==> min_val as int <= a@[j],
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