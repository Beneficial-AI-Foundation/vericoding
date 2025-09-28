// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn subtract_sequences(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] - b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used .index() for sequence access */
    Seq::new(a.len(), |i: int| a.index(i) - b.index(i))
}
// </vc-code>

}
fn main() {}