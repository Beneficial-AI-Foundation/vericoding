// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn not_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant 
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == (x1@[j] != x2@[j])
        decreases x1.len() - i
    {
        result.push(x1[i] != x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}