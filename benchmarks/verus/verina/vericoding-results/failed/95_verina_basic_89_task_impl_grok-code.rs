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
    /* code modified by LLM (iteration 5): fixed set union by replacing set_union with + operator for compilation */
    let mut result: Vec<i32> = Vec::new();
    let ghost seen = Set::empty();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@.len() == seen.view().len(),
            forall |k: int| 0 <= k < result@.len() ==> seen.view().contains(result@[k]),
            forall |k: int| 0 <= k < result@.len() ==> exists |j: int| 0 <= j < i && s@[j] == result@[k],
            forall |x: i32| seen.view().contains(x) ==> exists |j: int| 0 <= j < i && s@[j] == x
    {
        if !seen@.contains(s@[i]) {
            result.push(s[i]);
            proof {
                seen = seen + Set::singleton(s@[i]);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}