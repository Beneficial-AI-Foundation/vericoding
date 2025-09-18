// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation errors by using Seq::empty() and s.map() */
proof fn recursive_map_spec<A, B>(func: spec_fn(A) -> B, s: Seq<A>) -> Seq<B>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let rest = recursive_map_spec(func, s.subrange(0, s.len() - 1));
        let last_val = func(s.last());
        rest.push(last_val)
    }
}

proof fn recursive_map_lemma<A, B>(func: spec_fn(A) -> B, s: Seq<A>)
    ensures s.map(func) == recursive_map_spec(func, s),
    decreases s.len(),
{
    if s.len() > 0 {
        recursive_map_lemma(func, s.subrange(0, s.len() - 1));
    }
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
    /* code modified by LLM (iteration 5): used Vec::from_seq to bridge spec and exec */
    let result_seq = input@.map(func);
    let result = Vec::from_seq(result_seq);
    result
}
// </vc-code>

}
fn main() {}