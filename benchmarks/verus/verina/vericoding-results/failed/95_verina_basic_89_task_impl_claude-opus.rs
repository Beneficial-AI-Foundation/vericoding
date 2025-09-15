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
    /* code modified by LLM (iteration 5): fixed syntax error with invariant_except_break */
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
            forall|k: int| 0 <= k < result.len() ==> 
                exists|j: int| 0 <= j < i && s[j] == result[k],
            forall|k: int| 0 <= k < i ==> 
                exists|j: int| 0 <= j < result.len() && result[j] == s[k],
        decreases s.len() - i
    {
        let val = s[i];
        let mut found = false;
        let mut j = 0;
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found ==> exists|k: int| 0 <= k < result.len() && result[k] == val,
                !found ==> forall|k: int| 0 <= k < j ==> result[k] != val,
            ensures
                found ==> exists|k: int| 0 <= k < result.len() && result[k] == val,
                !found ==> forall|k: int| 0 <= k < result.len() ==> result[k] != val,
            decreases result.len() - j
        {
            if result[j] == val {
                found = true;
                assert(result[j] == val);
                assert(0 <= j < result.len());
                break;
            }
            j = j + 1;
        }
        if !found {
            result.push(val);
            assert(result[result.len() - 1] == val);
            assert(result[result.len() - 1] == s[i]);
        } else {
            assert(exists|k: int| 0 <= k < result.len() && result[k] == val);
            assert(exists|k: int| 0 <= k < result.len() && result[k] == s[i]);
        }
        i = i + 1;
    }
    assert(i == s.len());
    assert(forall|k: int| 0 <= k < s.len() ==> 
        exists|j: int| 0 <= j < result.len() && result[j] == s[k]);
    result
}
// </vc-code>

}
fn main() {}