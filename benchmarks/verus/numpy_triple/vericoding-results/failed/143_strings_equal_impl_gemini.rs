// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true <==> x1[i] == x2[i]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added asserts to guide proof for string equality */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == (x1@[j] == x2@[j]),
        decreases x1.len() - i
    {
        let eq = x1[i] == x2[i];
        result.push(eq);
        proof {
            // For a vector `v` of strings, `v[i] == v@[i]` holds by axiom.
            // For strings, `s1 == s2` is defined as `s1@ == s2@`.
            // This means `v[i]@ == (v@[i])@`, which we assert here to guide the prover.
            assert(x1[i]@ == (x1@[i as int])@);
            assert(x2[i]@ == (x2@[i as int])@);
            // With the above facts, we can now prove the property for the new element.
            assert(result@[i as int] == (x1@[i as int] == x2@[i as int]));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}