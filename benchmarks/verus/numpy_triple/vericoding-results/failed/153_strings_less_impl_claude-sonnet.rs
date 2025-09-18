// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): mark as uninterp and provide single definition */
spec fn str_less_than(s1: String, s2: String) -> bool
    uninterp;

proof fn lemma_str_less_than_properties(s1: String, s2: String)
    ensures s1 == s2 ==> !str_less_than(s1, s2),
            str_less_than(s1, s2) ==> !str_less_than(s2, s1),
            str_less_than(s1, s2) ==> s1 != s2
{
}
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
    /* code modified by LLM (iteration 5): fix indexing and casting issues */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == str_less_than(x1@[j], x2@[j])
    {
        let comparison = str_less_than(x1[i], x2[i]);
        result.push(comparison);
        
        proof {
            lemma_str_less_than_properties(x1[i], x2[i]);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}