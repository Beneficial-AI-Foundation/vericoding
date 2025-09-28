// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed trigger syntax error by removing trigger from invariant condition */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
            forall|k: int| 0 <= k < result.len() ==> 
                exists|j: int| 0 <= j < i && s[j] == result[k],
            forall|k: int| 0 <= k < i ==> 
                exists|j: int| 0 <= j < result.len() && result[j] == s[k] ||
                exists|l: int| i <= l < s.len() && s[l] == s[k],
        decreases s.len() - i
    {
        let mut found = false;
        let mut j: usize = 0;
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                forall|k: int| 0 <= k < j ==> result[k] != s[i as int],
                !found,
            decreases result.len() - j
        {
            if result[j] == s[i] {
                found = true;
                break;
            }
            j = j + 1;
        }
        if !found {
            result.push(s[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}