// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provides a spec-level contains predicate for Vec<char> */
spec fn vec_contains(v: &Vec<char>, c: char) -> bool { v@.contains(#[trigger] c) }
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
{
    /* code modified by LLM (iteration 5): iterate over str1 using nat indices and build result excluding chars in str2 */
    let mut result: Vec<char> = Vec::new();
    let mut i: nat = 0;
    while i < str1@.len()
        invariant
            0 <= i,
            i <= str1@.len(),
            forall|j: nat| 0 <= j && j < result@.len() ==> (str1@.contains(#[trigger] (result@)[j]) && !str2@.contains(#[trigger] (result@)[j])),
            forall|k: nat| 0 <= k && k < i ==> (str2@.contains(#[trigger] (str1@)[k]) || result@.contains(#[trigger] (str1@)[k])),
        decreases str1@.len() - i
    {
        let c: char = (str1@)[i];
        if !str2@.contains(#[trigger] c) {
            result.push(c);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}