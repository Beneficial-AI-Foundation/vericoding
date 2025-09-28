// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_element(s: &Vec<i32>, elem: i32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == elem
}

/* helper modified by LLM (iteration 5): added proof for final postcondition satisfaction */
proof fn prove_all_elements_included(s: &Vec<i32>, result: &Vec<i32>, processed: int)
    requires
        0 <= processed <= s.len(),
        forall|x: int| 0 <= x < processed ==> 
            exists|y: int| 0 <= y < result.len() && result[y] == #[trigger] s[x]
    ensures
        forall|x: int| 0 <= x < processed ==> 
            exists|y: int| 0 <= y < result.len() && result[y] == #[trigger] s[x]
{}
// </vc-helpers>

// <vc-spec>
fn set_to_seq(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],

        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] result[i],

        forall|i: int| 0 <= i < s.len() ==> 
            exists|j: int| 0 <= j < result.len() && result[j] == #[trigger] s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant and added proof to establish final postcondition */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] != result[y],
            forall|x: int| 0 <= x < result.len() ==> 
                exists|y: int| 0 <= y < s.len() && s[y] == #[trigger] result[x],
            forall|x: int| 0 <= x < i ==> 
                exists|y: int| 0 <= y < result.len() && result[y] == #[trigger] s[x]
        decreases s.len() - i
    {
        let current = s[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found == exists|k: int| 0 <= k < j && result[k] == current
            decreases result.len() - j
        {
            if result[j] == current {
                found = true;
            }
            j += 1;
        }
        
        if !found {
            result.push(current);
            proof {
                assert(result[result.len() - 1] == current);
                assert(current == s[i]);
            }
        }
        
        i += 1;
    }
    
    proof {
        prove_all_elements_included(s, &result, s.len() as int);
    }
    
    result
}
// </vc-code>

}
fn main() {}