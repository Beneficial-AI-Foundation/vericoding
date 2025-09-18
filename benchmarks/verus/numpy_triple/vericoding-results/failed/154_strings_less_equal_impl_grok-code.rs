// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): implemented spec functions for string less equal comparison */
spec fn str_leq(s1: Seq<char>, s2: Seq<char>) -> bool
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 {
        true
    } else if s2.len() == 0 {
        false
    } else if s1[0] < s2[0] {
        true
    } else if s1[0] == s2[0] {
        str_leq(s1.slice(1, s1.len() as int), s2.slice(1, s2.len() as int))
    } else {
        false
    }
}

spec fn string_le(s1: String, s2: String) -> bool {
    str_leq(s1.view(), s2.view())
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
/* code modified by LLM (iteration 2): implemented loop to fill result vector with less_equal comparisons */
{
    let mut result = Vec::new();
    for i in 0..x1.len()
        invariant 0 <= i <= x1.len(),
            result.len() == i as nat,
            forall|j: int| 0 <= j < i ==> result[j] == string_le(x1[j], x2[j])
    {
        result.push(string_le(x1[i], x2[i]));
    }
    result
}
// </vc-code>

}
fn main() {}