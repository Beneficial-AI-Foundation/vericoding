// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper to index sequences */
spec fn seq_index(xs: &Seq<i32>, i: nat) -> i32 { xs@[i] }
// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement to_array using loop and seq_index helper */
    let mut result: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < xs.len()
        invariant i <= xs.len();
        invariant result.len() == i;
        invariant forall|j: nat| j < i ==> result[j] == seq_index(xs, j);
        decreases xs.len() - i
    {
        result.push(seq_index(xs, i));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}