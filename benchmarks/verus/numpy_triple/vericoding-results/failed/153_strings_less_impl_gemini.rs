// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): defined str_less_than which was previously uninterpreted */
spec fn str_less_than(s1: String, s2: String) -> bool { s1 < s2 }
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
    /* code modified by LLM (iteration 5): added invariants mirroring postconditions to guide verification */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == str_less_than(x1[j], x2[j]),
            forall|j: int| 0 <= j < i && result[j] == true ==> !str_less_than(x2[j], x1[j]),
            forall|j: int| 0 <= j < i && x1[j] == x2[j] ==> result[j] == false,
            forall|j: int| 0 <= j < i && result[j] == true ==> x1[j] != x2[j],
            forall|j: int| 0 <= j < i ==> result[j] == true || x1[j] == x2[j] || str_less_than(x2[j], x1[j])
        decreases x1.len() - i
    {
        proof {
            vstd::string::lemma_string_ordering_is_trichotomous(x1[i], x2[i]);
        }
        let b = x1[i] < x2[i];
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}