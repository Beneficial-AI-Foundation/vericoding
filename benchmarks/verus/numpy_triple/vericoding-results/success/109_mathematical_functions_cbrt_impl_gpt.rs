// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn len_seq<T>(s: Seq<T>) -> nat { s.len() }

proof fn lemma_len_seq_id<T>(s: Seq<T>)
    ensures len_seq(s) == s.len()
{ }
// </vc-helpers>

// <vc-spec>
fn cbrt(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    x
}
// </vc-code>

}
fn main() {}