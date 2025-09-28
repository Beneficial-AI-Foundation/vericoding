// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Corrected the path to the lemma `lemma_get_is_mem`, which is in `vstd::seq_lib`, not `vstd::seq`. */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < result.len() ==> (str1@.contains(#[trigger] result@[k]) && !str2@.contains(#[trigger] result@[k])),
            forall|k: int| 0 <= k < i ==> (str2@.contains(#[trigger] str1@[k]) || result@.contains(#[trigger] str1@[k])),
    {
        let c = str1[i];
        if !str2.contains(&c) {
            proof {
                vstd::seq_lib::lemma_get_is_mem(str1@, i as int);
            }
            result.push(c);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}