// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple lemma converting not-less to less-or-equal */
proof fn not_lt_implies_le(x: int, y: int) {
    assert(!(x < y) ==> y <= x);
}

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
/* code modified by LLM (iteration 3): iterative search that returns insertion index */
{
    let mut i: usize = 0;
    while i < xs.len() && xs[i] < target
        invariant
            0 <= i as int,
            i as int <= xs.len() as int,
            forall|j: int| 0 <= j < i as int ==> xs[j] < target,
        decreases xs.len() as int - i as int
    {
        i = i + 1;
    }
    i
}

// </vc-code>

}
fn main() {}