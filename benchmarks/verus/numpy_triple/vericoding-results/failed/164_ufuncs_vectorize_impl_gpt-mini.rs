// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): map Seq<A> to Seq<B> applying spec_fn */
spec fn seq_map<A, B>(f: spec_fn(A) -> B, s: Seq<A>) -> Seq<B> { Seq::new(s.len(), |i: int| f(s[i])) }
// </vc-helpers>

// <vc-spec>
fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): convert Vec to Seq, map f, and build Vec from Seq */
    let s: Seq<B> = seq_map(f, arr@);
    Vec::from_seq(s)
}
// </vc-code>

}
fn main() {}