// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define sequence mapping helper */
spec fn map_seq<A, B>(f: spec_fn(A) -> B, s: Seq<A>) -> Seq<B> {
    Seq::new(s.len(), |i: int| f(s[i]))
}

/* helper modified by LLM (iteration 5): map_seq preserves length */
proof fn map_seq_len<A, B>(f: spec_fn(A) -> B, s: Seq<A>)
    ensures
        map_seq(f, s).len() == s.len()
{ }

/* helper modified by LLM (iteration 5): pointwise characterization of map_seq */
proof fn map_seq_index<A, B>(f: spec_fn(A) -> B, s: Seq<A>, i: int)
    requires
        0 <= i < s.len()
    ensures
        map_seq(f, s)[i] == f(s[i])
{ }
// </vc-helpers>

// <vc-spec>
fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix ghost arg usage and construct result from spec mapping */
    let ghost s: Seq<B> = map_seq(f, arr@);
    let v: Vec<B> = Vec::from_spec_seq(s);
    v
}
// </vc-code>

}
fn main() {}