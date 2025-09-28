// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    ensures
        result <= a.len(),
        result == a.len() || a[result as int] == e,
        forall|i: int| 0 <= i < result ==> a[i] != e,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant // TODO: Fix: `loop_invariant_pack` for `while` loops doesn't unpack into multiple invariants. Instead they unpack into conjunctions of conditions, and they're expected to be in curly braces
            0 <= i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    a.len()
}
// </vc-code>

}
fn main() {}