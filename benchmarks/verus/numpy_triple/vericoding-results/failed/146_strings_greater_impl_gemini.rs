// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed string_compare_gt redefinition and fixed lemma path */
proof fn lemma_gt_antisymmetric(s1: Seq<char>, s2: Seq<char>)
    requires string_compare_gt(s1, s2)
    ensures !string_compare_gt(s2, s1)
{
    if string_compare_gt(s2, s1) {
        vstd::seq_lib::lemma_is_le_antisymm(s1, s2);
        assert(false);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn string_compare_gt(s1: Seq<char>, s2: Seq<char>) -> bool;

fn greater(x1: &Vec<String>, x2: &Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == string_compare_gt(x1[i]@, x2[i]@),

        forall|i: int| 0 <= i < result.len() ==> 
            result[i] ==> !string_compare_gt(x2[i]@, x1[i]@),

        forall|i: int| 0 <= i < result.len() ==> 
            (x1[i]@ == x2[i]@) ==> (result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The logic from the previous iteration was correct. */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_compare_gt(x1[j]@, x2[j]@),
            forall|j: int| 0 <= j < i ==> result[j] ==> !string_compare_gt(x2[j]@, x1[j]@),
            forall|j: int| 0 <= j < i ==> (x1[j]@ == x2[j]@) ==> (result[j] == false),
    {
        let s1 = &x1[i];
        let s2 = &x2[i];
        let is_gt = s1.gt(s2);
        
        if is_gt {
            proof {
                lemma_gt_antisymmetric(s1@, s2@);
            }
        }

        result.push(is_gt);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}