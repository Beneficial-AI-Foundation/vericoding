// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed type conversion issues and implemented string comparison */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_compare_gt(x1[j]@, x2[j]@),
            forall|j: int| 0 <= j < i ==> result[j] ==> !string_compare_gt(x2[j]@, x1[j]@),
            forall|j: int| 0 <= j < i ==> (x1[j]@ == x2[j]@) ==> (result[j] == false),
    {
        let s1 = &x1[i];
        let s2 = &x2[i];
        let s1_chars = s1@;
        let s2_chars = s2@;
        
        let mut cmp_result = false;
        let mut j: usize = 0;
        let s1_len = s1_chars.len();
        let s2_len = s2_chars.len();
        let min_len = if s1_len < s2_len { s1_len } else { s2_len };
        
        while j < min_len
            invariant
                0 <= j <= min_len,
                min_len <= s1_chars.len(),
                min_len <= s2_chars.len(),
        {
            let c1 = s1.as_bytes()[j];
            let c2 = s2.as_bytes()[j];
            if c1 > c2 {
                cmp_result = true;
                break;
            } else if c1 < c2 {
                cmp_result = false;
                break;
            }
            j = j + 1;
        }
        
        if j == min_len && !cmp_result {
            if s1_len > s2_len {
                cmp_result = true;
            }
        }
        
        result.push(cmp_result);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}