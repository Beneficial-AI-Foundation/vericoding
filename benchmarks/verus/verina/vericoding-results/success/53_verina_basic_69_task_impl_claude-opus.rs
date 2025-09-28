// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures
        result < a.len(),
        a[result as int] == e,
        forall|k: int| 0 <= k < result ==> a[k] != e,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] != e,
            exists|j: int| i <= j < a.len() && a[j] == e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}