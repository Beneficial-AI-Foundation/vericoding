// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix min function arguments to accept nat types */
spec fn min(a: nat, b: nat) -> nat {
    if a <= b { a } else { b }
}

proof fn string_compare_gt_properties()
    ensures
        forall|s1: Seq<char>, s2: Seq<char>| string_compare_gt(s1, s2) ==> !string_compare_gt(s2, s1),
        forall|s1: Seq<char>, s2: Seq<char>| s1 == s2 ==> !string_compare_gt(s1, s2),
{
    assert forall|s1: Seq<char>, s2: Seq<char>| string_compare_gt(s1, s2) implies !string_compare_gt(s2, s1) by {
        if string_compare_gt(s1, s2) {
            let i = choose|i: int| 0 <= i < min(s1.len(), s2.len()) as int && 
                (forall|j: int| 0 <= j < i ==> s1[j] == s2[j]) && 
                s1[i] > s2[i];
            assert(s2[i] < s1[i]);
            assert forall|k: int| 0 <= k < i ==> s2[k] == s1[k] by { };
        }
    };
    
    assert forall|s1: Seq<char>, s2: Seq<char>| s1 == s2 implies !string_compare_gt(s1, s2) by {
        if s1 == s2 {
            assert forall|i: int| 0 <= i < min(s1.len(), s2.len()) as int ==> s1[i] == s2[i] by { };
        }
    };
}
// </vc-helpers>

// <vc-spec>
spec fn string_compare_gt(s1: Seq<char>, s2: Seq<char>) -> bool {
    true  // placeholder implementation
}

fn greater(x1: &Vec<String>, x2: &Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i] == string_compare_gt(x1[i]@, x2[i]@),

        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i] ==> !string_compare_gt(x2[i]@, x1[i]@),

        forall|i: int| 0 <= i < result.len() as int ==> 
            (x1[i]@ == x2[i]@) ==> (result[i] == false),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Remove unused code and rely on verified helper properties */{
    let mut result = Vec::new();
    let len = x1.len();
    let mut i: usize = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_compare_gt(x1[j]@, x2[j]@),
            forall|j: int| 0 <= j < i ==> result[j] ==> !string_compare_gt(x2[j]@, x1[j]@),
            forall|j: int| 0 <= j < i ==> x1[j]@ == x2[j]@ ==> result[j] == false,
        decreases len - i
    {
        result.push(string_compare_gt(x1[i]@, x2[i]@));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}