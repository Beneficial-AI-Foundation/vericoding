// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected seq access to use exec-style indexing */
fn contains_exec(seq: Seq<int>, val: int) -> (b: bool)
    ensures b <==> seq.contains(val)
{
    let mut i: usize = 0;
    while i < seq.len() as usize
        invariant
            !seq.subrange(0, i as nat).contains(val),
        decreases (seq.len() as usize) - i
    {
        if seq[i] == val {
            return true;
        }
        i = i + 1;
    }
    false
}

/* helper modified by LLM (iteration 5): Corrected seq access to use exec-style indexing */
fn any_value_exists_rec(seq1: Seq<int>, seq2: Seq<int>, i: usize) -> (result: bool)
    requires
        i as nat <= seq1.len(),
    ensures
        result <==> (exists|k: nat| i as nat <= k < seq1.len() && seq2.contains(seq1@[k])),
    decreases (seq1.len() as usize) - i
{
    if i < seq1.len() as usize {
        if contains_exec(seq2, seq1[i]) {
            true
        } else {
            any_value_exists_rec(seq1, seq2, i + 1)
        }
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn any_value_exists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < seq1.len() && seq2.contains(seq1[i]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed as the logic correctly calls the helper. */
{
    any_value_exists_rec(seq1, seq2, 0)
}
// </vc-code>

}
fn main() {}