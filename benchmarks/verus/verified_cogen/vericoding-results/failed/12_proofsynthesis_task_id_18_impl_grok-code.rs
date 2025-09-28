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
    /* code modified by LLM (iteration 5): Fixed compilation errors by correcting trigger syntax and vector indexing in invariants */
    let mut result = Vec::new();
    let mut i = 0;
    while i < str1.len()
        invariant
            i <= str1.len(),
            forall |j: int| 0 <= j < i ==> #[trigger] str2@.contains(str1@[j]) || result@.contains(#[trigger] str1@[j]),
            forall |k: int| 0 <= k < result.len() ==> #[trigger] str1@.contains(#[trigger] result@[k]) && !str2@.contains(result@[k])
        decreases str1.len() - i
    {
        let ch = str1[i];
        let mut found = false;
        let mut k = 0;
        while k < str2.len()
            decreases str2.len() - k
        {
            if str2[k] == ch {
                found = true;
                break;
            }
            k += 1;
        }
        if !found {
            proof {
                assert(str1@.contains(ch));
                assert(!str2@.contains(ch));
            }
            result.push(ch);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}