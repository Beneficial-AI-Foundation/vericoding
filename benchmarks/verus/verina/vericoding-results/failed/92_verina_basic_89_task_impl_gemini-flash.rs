// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add decreases to contains loop */
fn contains(s: &Vec<i32>, value: i32, len: usize) -> (b: bool)
    requires
        len <= s.len(),
    ensures
        b == (exists|i: int| 0 <= i < len as int && s[i] == value)
{
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            forall|j: int| 0 <= j < i as int ==> s[j] != value,
        decreases len - i
    {
        if s[i] == value {
            return true;
        }
        i = i + 1;
    }
    false
}

proof fn lemma_distinct_elements_in_subset(s: &Vec<i32>, start: int, end: int)
    requires
        0 <= start <= end <= s.len() as int,
        forall|i: int, j: int| start <= i < j < end ==> s[i] != s[j],
    ensures
        forall|k: int| start <= k < end ==> forall|l: int| start <= l < k ==> s[l] != s[k],
{
    // No proof steps needed, this is trivially true by reordering quantifiers.
    // The original ensures condition: (for all i, j where i < j, s[i] != s[j]) implies
    // (for all k, for all l where l < k, s[l] != s[k]).
    // Both express that all elements in the range [start, end) are unique.
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
/* code modified by LLM (iteration 5): add decreases to main loop */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let s_len = s.len();
    while i < s_len
        invariant
            i <= s_len,
            result.len() <= s_len,
            forall|k: int, l: int| 0 <= k < l < result.len() as int ==> result[k] != result[l],
            forall|k: int| 0 <= k < result.len() as int ==> exists|j: int| 0 <= j < s_len as int && s[j] == result[k],
            forall|k: int| 0 <= k < i as int ==> exists|l: int| 0 <= l < result.len() as int && result[l] == s[k],
        decreases s_len - i
    {
        let current_val = s[i];
        if !contains(&result, current_val, result.len()) {
            result.push(current_val);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}