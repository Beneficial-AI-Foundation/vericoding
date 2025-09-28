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
    /* code modified by LLM (iteration 2): replaced unreachable!() with proper loop termination */
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] != e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i += 1;
    }
    proof {
        assert(false);
    }
    0
}
// </vc-code>

}
fn main() {}