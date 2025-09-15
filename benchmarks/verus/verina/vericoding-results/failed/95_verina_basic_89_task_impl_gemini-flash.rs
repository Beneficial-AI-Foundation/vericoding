// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed distinct_elements_in_vec as it was not used and the distinctness is handled by the main function's logic. */
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
/* code modified by LLM (iteration 5): Fixed type mismatches in quantifiers by adjusting `s` and `result` indexing to use `int` where necessary, assuming `Vec<i32>` elements are directly comparable. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i as int && i as int <= s.len() as int,
            // The following ensures distinctness in `result` directly.
            forall|idx: int, jdx: int| 0 <= idx < jdx < result.len() ==> result[idx] != result[jdx],
            // Each element in `result` must be present in the original `s` up to index `i`.
            forall|idx: int| 0 <= idx < result.len() ==> exists|jdx: int| 0 <= jdx < i as int && s.get_By_index(jdx) == #[trigger] result.get_By_index(idx),
            // Each element in `s` up to index `i` must be present in `result` if it's considered.
            forall|idx: int| 0 <= idx < i as int ==> exists|jdx: int| 0 <= jdx < result.len() && result.get_By_index(jdx) == #[trigger] s.get_By_index(idx)
        decreases (s.len() - i) as int
    {
        let current_val = s[i];
        let mut found = false;
        let mut k: usize = 0;
        while k < result.len()
            invariant
                0 <= k as int && k as int <= result.len() as int,
                !found ==> forall|idx: int| 0 <= idx < k as int ==> result.get_By_index(idx) != current_val
            decreases (result.len() - k) as int
        {
            if result[k] == current_val {
                found = true;
            }
            k = k + 1;
        }

        if !found {
            result.push(current_val);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}