// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding `use vstd::vec::*` to ensure `Vec` is available within helper functions if needed. */
use vstd::vec::*;
// </vc-helpers>

// <vc-spec>
fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)

    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by replacing `vstd::vec::Vec::new()` with `Vec::new()` after ensuring `Vec` is properly imported via `use vstd::vec::*` in helpers. */
{
    let mut result_vec = Vec::new();
    let mut i: int = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|j: int| 0 <= j < result_vec.len() ==> (
                str1@.contains(#[trigger] result_vec[j]) && !str2@.contains(result_vec[j])
            ),
            forall|j: int| 0 <= j < i ==> (
                str2@.contains(str1[j]) || result_vec@.contains(str1[j])
            ),
            result_vec.len() <= str1.len(),
    {
        let current_char = str1@[i];
        if !str2@.contains(current_char) {
            result_vec.push(current_char);
        }
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}