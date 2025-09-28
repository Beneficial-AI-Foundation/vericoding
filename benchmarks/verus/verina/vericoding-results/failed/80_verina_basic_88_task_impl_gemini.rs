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
    /* code modified by LLM (iteration 3): fixed compilation error in loop condition and types in invariants */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < xs.len() as usize
        invariant
            (i as nat) <= xs.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result.view()[j] == xs[j],
        decreases xs.len() - (i as nat)
    {
        // This push is logically incorrect, but resolves the current compilation error.
        // The resulting verification error will be addressed in the next step.
        result.push(0);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}