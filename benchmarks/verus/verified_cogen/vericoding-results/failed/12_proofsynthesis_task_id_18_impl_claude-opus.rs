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
    /* code modified by LLM (iteration 5): fixed indexing and invariant issues */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|j: int| 0 <= j < result.len() ==> (str1@.contains(#[trigger] result[j]) && !str2@.contains(#[trigger] result[j])),
            forall|j: int| 0 <= j < i ==> (str2@.contains(#[trigger] str1[j]) || result@.contains(#[trigger] str1[j]))
        decreases str1.len() - i
    {
        let mut found = false;
        let mut j: usize = 0;
        while j < str2.len()
            invariant
                0 <= i < str1.len(),
                0 <= j <= str2.len(),
                found <==> exists|k: int| 0 <= k < j && str2[k] == str1[i as int]
            decreases str2.len() - j
        {
            if str2[j] == str1[i] {
                found = true;
                proof {
                    assert(exists|k: int| 0 <= k < j + 1 && str2[k] == str1[i as int]) by {
                        assert(str2[j as int] == str1[i as int]);
                    }
                }
                break;
            }
            j = j + 1;
        }
        if !found {
            result.push(str1[i]);
            proof {
                assert(forall|j: int| 0 <= j < result.len() ==> (str1@.contains(#[trigger] result[j]) && !str2@.contains(#[trigger] result[j]))) by {
                    assert(str1@.contains(str1[i]));
                    assert(!str2@.contains(str1[i]));
                }
            }
        }
        proof {
            assert(str2@.contains(str1[i]) || result@.contains(str1[i]));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}