// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches and sequence indexing */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == xs[j],
        decreases xs.len() - i
    {
        result.push(xs[i as int]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}