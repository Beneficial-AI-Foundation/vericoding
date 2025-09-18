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
    /* code modified by LLM (iteration 5): Changed index variable from usize to int for proper Verus sequence indexing */
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < x1.len()
        invariant
            i >= 0,
            result.len() as int == i,
            forall |j: int| 0 <= j < i ==> result@[j] == (x1@[j] != x2@[j])
        decreases x1.len() - i
    {
        result.push(x1@[i] != x2@[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}