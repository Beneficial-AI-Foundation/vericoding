// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
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
    /* code modified by LLM (iteration 5): added lemma to prove string equality equivalence */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] != x2[j]),
        decreases x1.len() - i
    {
        proof {
            vstd::string::lemma_string_properties(x1[i], x2[i]);
        }
        let ne = x1[i] != x2[i];
        result.push(ne);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}