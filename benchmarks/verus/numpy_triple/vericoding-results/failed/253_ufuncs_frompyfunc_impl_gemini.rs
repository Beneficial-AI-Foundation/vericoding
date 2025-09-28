// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn map_seq<A, B>(s: Seq<A>, f: spec_fn(A) -> B) -> Seq<B>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        seq![f(s.first())].add(map_seq(s.drop_first(), f))
    }
}

/* helper modified by LLM (iteration 4): changed to broadcast proof fn and added triggers */
broadcast proof fn lemma_map_seq_properties<A, B>(s: Seq<A>, f: spec_fn(A) -> B)
    ensures
        #[trigger] map_seq(s, f).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] map_seq(s, f)[i] == f(s[i]),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_map_seq_properties(s.drop_first(), f);
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_frompyfunc(func: spec_fn(i8) -> i8, input: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> result[i] == func(input[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clause and implemented loop logic */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == func(input[j]),
        decreases input.len() - i
    {
        let transformed_item = func(input[i]);
        result.push(transformed_item);
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}