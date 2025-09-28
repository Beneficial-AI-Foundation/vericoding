// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed invariant to properly track character presence */
fn vec_contains_char(vec: &Vec<char>, c: char) -> (result: bool)
    ensures result == vec@.contains(c)
{
    let mut i = 0;
    while i < vec.len()
        invariant
            0 <= i <= vec.len(),
            !vec@.subrange(0, i as int).contains(c),
        decreases vec.len() - i
    {
        if vec[i] == c {
            proof {
                assert(vec@.subrange(0, (i + 1) as int).contains(c));
                assert(vec@.contains(c));
            }
            return true;
        }
        i += 1;
    }
    proof {
        assert(i == vec.len());
        assert(vec@.subrange(0, i as int) == vec@);
        assert(!vec@.contains(c));
    }
    false
}
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
    /* code modified by LLM (iteration 5): fixed invariants to properly handle character tracking */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|j: int| 0 <= j < result.len() ==> (str1@.contains(result[j]) && !str2@.contains(result[j])),
            forall|j: int| 0 <= j < i ==> (str2@.contains(str1[j]) || result@.contains(str1[j])),
        decreases str1.len() - i
    {
        let c = str1[i];
        if !vec_contains_char(str2, c) {
            result.push(c);
            proof {
                assert(str1@.contains(c));
                assert(!str2@.contains(c));
                assert(result@.contains(c));
            }
        } else {
            proof {
                assert(str2@.contains(c));
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}