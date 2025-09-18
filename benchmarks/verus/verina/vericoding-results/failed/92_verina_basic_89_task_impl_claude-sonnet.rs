// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof block to establish relationship between contains and actual element presence */
spec fn contains(v: Vec<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < v.len() && #[trigger] v[i] == val
}

fn contains_exec(v: &Vec<i32>, val: i32) -> (result: bool)
    ensures
        result == contains(*v, val),
        result ==> exists|i: int| 0 <= i < v.len() && v[i] == val,
        !result ==> forall|i: int| 0 <= i < v.len() ==> v[i] != val,
{
    for i in 0..v.len()
        invariant
            forall|j: int| 0 <= j < i ==> v[j] != val,
    {
        if v[i] == val {
            return true;
        }
    }
    false
}
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
    /* code modified by LLM (iteration 5): added proof blocks to establish postcondition satisfaction */
    let mut result = Vec::new();
    
    for i in 0..s.len()
        invariant
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
            forall|k: int| 0 <= k < result.len() ==> 
                exists|j: int| 0 <= j < s.len() && #[trigger] s[j] == #[trigger] result[k],
            forall|k: int| 0 <= k < i ==> 
                exists|j: int| 0 <= j < result.len() && #[trigger] result[j] == #[trigger] s[k],
    {
        let old_result = result;
        if !contains_exec(&result, s[i]) {
            result.push(s[i]);
            
            proof {
                assert(result.len() == old_result.len() + 1);
                assert(result[result.len() - 1] == s[i]);
                assert(forall|k: int| 0 <= k < old_result.len() ==> result[k] == old_result[k]);
                assert(exists|j: int| 0 <= j < result.len() && result[j] == s[i]);
            }
        } else {
            proof {
                assert(exists|j: int| 0 <= j < result.len() && result[j] == s[i]);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}