// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate `string_le` declaration. */
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
/* code modified by LLM (iteration 5): No changes to code body, previous iteration fixed it correctly. */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < x1.len()
        invariant
            0 <= i as int && i as int <= x1.len() as int,
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i as int ==> result[j] == string_le(x1[j as usize], x2[j as usize]),
    {
        result.push(string_le(x1[i], x2[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}