// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): wrapper to refer to spec str_less_than without redefining it */
spec fn str_less_than_wrapper(s1: String, s2: String) -> bool { str_less_than(s1, s2) }
// </vc-helpers>

// <vc-spec>
spec fn str_less_than(s1: String, s2: String) -> bool;

fn less(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() ==> result[i] == str_less_than(x1[i], x2[i]),

        forall|i: int| 0 <= i < result.len() && result[i] == true ==> !str_less_than(x2[i], x1[i]),

        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == false,

        forall|i: int| 0 <= i < result.len() ==> result[i] == true || result[i] == false,

        forall|i: int| 0 <= i < result.len() && result[i] == true ==> x1[i] != x2[i],

        forall|i: int| 0 <= i < result.len() ==> result[i] == true || x1[i] == x2[i] || str_less_than(x2[i], x1[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result vector with elementwise str_less_than and maintain prefix invariant */
    let n = x1.len();
    let mut result: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant result.len() == j,
        invariant forall|k: int| 0 <= k < j as int ==> result[k] == str_less_than(x1[k], x2[k]),
        decreases n - j
    {
        result.push(str_less_than(x1[j], x2[j]));
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}