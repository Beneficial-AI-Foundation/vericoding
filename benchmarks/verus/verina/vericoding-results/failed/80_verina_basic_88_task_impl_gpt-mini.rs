// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): spec helpers for Seq length and indexing */
spec fn seq_len(xs: &Seq<i32>) -> nat { xs.len() }
spec fn seq_index(xs: &Seq<i32>, i: nat) -> i32 { xs.index(i) }
// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): convert Seq to Vec using nat indices */
    let mut result: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < seq_len(xs)
        invariant
            0 <= i,
            i <= seq_len(xs),
            result.len() == i,
            forall|j: nat| 0 <= j < i ==> result[j] == seq_index(xs, j),
        decreases seq_len(xs) - i
    {
        result.push(seq_index(xs, i));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}