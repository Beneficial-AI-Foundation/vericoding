// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5: defined string_le using lexicographic order) */
spec fn string_le(s1: String, s2: String) -> bool {
    s1@ <= s2@
}
// </vc-helpers>

// <vc-spec>
spec fn string_le(s1: String, s2: String) -> bool;

fn less_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == string_le(x1[i], x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true <==> string_le(x1[i], x2[i])),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,
        forall|i: int| 0 <= i < result.len() ==> (string_le(x1[i], x2[i]) && string_le(x2[i], x1[i])) ==> x1[i] == x2[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5: changed invariant to use string_le) */
{
    let mut result = Vec::with_capacity(x1.len());
    for i in 0..x1.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_le(x1[j], x2[j]),
    {
        let b = x1[i] <= x2[i];
        result.push(b);
    }
    result
}
// </vc-code>

}
fn main() {}