// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): retained trivial helper for structure; no additional lemmas needed */
proof fn helper_trivial() { }
// </vc-helpers>

// <vc-spec>
fn search_insert(xs: &Vec<i32>, target: i32) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
    ensures
        result <= xs.len(),
        forall|i: int| 0 <= i < result ==> xs[i] < target,
        result < xs.len() ==> target <= xs[result as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix spec indexing and cast types to int in assertions and invariants */
    let mut i: usize = 0;
    while i < xs.len() && xs[i] < target
        invariant
            i <= xs.len(),
            forall|j: int| 0 <= j < i as int ==> xs[j] < target,
        decreases (xs.len() - i) as int
    {
        i += 1;
    }
    if i < xs.len() {
        assert((target as int) <= xs[i as int]);
    }
    i
}
// </vc-code>

}
fn main() {}