// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define spec map over sequences (length-preserving) */
spec fn map_seq<A, B>(s: Seq<A>, f: spec_fn(A) -> B) -> Seq<B> {
    Seq::<B>::new(s.len(), |i: int| f(s[i]))
}

/* helper modified by LLM (iteration 5): lemma about index of map_seq */
proof fn map_seq_indexed<A, B>(s: Seq<A>, f: spec_fn(A) -> B, i: int)
    requires
        0 <= i < s.len()
    ensures
        map_seq(s, f)[i] == f(s[i])
{
}
// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc<A, B>(func: spec_fn(A) -> B, input: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct Vec from spec sequence using vstd::vec::Vec::from_seq to avoid std::convert::From */
    let s: Seq<B> = map_seq(input@, func);
    let result = vstd::vec::Vec::<B>::from_seq(s);
    result
}
// </vc-code>

}
fn main() {}