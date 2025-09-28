// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The problem is that array indexing (s[k]) expects a usize type, but k is an int type. To fix this, change the type of k from int to usize */

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
/* code modified by LLM (iteration 5): Fix for the type mismatch in array indexing, where s[k as usize] and result[j as usize] expects an int type, where it is of usize type. This has been fixed by simply removing the unnecessary type conversions. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant 
            0 <= i as int <= s.len() as int,
            forall|j: int, k: int| 0 <= j < k < result.len() as int ==> result[j] != result[k],
            forall|j: int| 0 <= j < result.len() as int ==> 
                exists|k: int| 0 <= k < i as int && s[k] as int == #[trigger] result[j] as int,
            forall|j: int| 0 <= j < i as int ==> 
                exists|k: int| 0 <= k < result.len() as int && result[k] as int == #[trigger] s[j] as int,
    {
        let mut contains = false;
        let mut j = 0;
        while j < result.len()
            invariant
                0 <= j as int <= result.len() as int,
                !contains ==> forall|k_inner: int| 0 <= k_inner < j as int ==> result[k_inner] != s[i],
        {
            if result[j] == s[i] {
                contains = true;
                break;
            }
            j = j + 1;
        }

        if !contains {
            result.push(s[i]);
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}