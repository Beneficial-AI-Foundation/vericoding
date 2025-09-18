// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn apply_func<A, B>(func: spec_fn(A) -> B, seq: Seq<A>) -> Seq<B> {
    Seq::new(seq.len(), |i: int| func(seq[i]))
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
    let seq_input: Seq<A> = Seq::new(input.len(), |i: int| input[i]);
    let seq_result: Seq<B> = apply_func(func, seq_input);
    let result: Vec<B> = seq_result.to_vec();
    result
}
// </vc-code>

}
fn main() {}