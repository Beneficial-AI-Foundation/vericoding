// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): still no helper needed */
// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use builtin conversion and proper sequence indexing */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let len = xs.len();
    while i < len
        invariant
            i <= xs.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as int] == xs[j],
    {
        proof {
            assert(i < xs.len());
        }
        result.push(xs[i as int]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}