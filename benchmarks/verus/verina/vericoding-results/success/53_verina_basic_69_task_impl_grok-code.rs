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
    /* code modified by LLM (iteration 3): implemented linear search loop with proper while condition */
    let mut i: usize = 0;
    while i < a.len() && a[i] != e
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k as int] != e,
        decreases (a.len() - i) as nat
    {
        i += 1;
    }
    return i;
}
// </vc-code>

}
fn main() {}