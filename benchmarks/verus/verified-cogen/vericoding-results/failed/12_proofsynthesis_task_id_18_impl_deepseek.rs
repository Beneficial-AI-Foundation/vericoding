// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added is_char_in_vec function to fix compilation error */
fn is_char_in_vec(c: char, v: &Vec<char>) -> bool {
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
    {
        if v[i] == c {
            return true;
        }
        i += 1;
    }
    false
}

/* helper modified by LLM (iteration 4): Fixed contains_lemma parameter to use reference instead of clone */
proof fn contains_lemma(v: &Vec<char>, c: char)
    ensures v@.contains(c) ==> exists|i: int| 0 <= i < v.len() && v@[i] == c
{
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
/* code modified by LLM (iteration 5): Fixed compilation error by using is_char_in_vec helper */
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|k: int| 0 <= k < result.len() ==> (str1@.contains(result@[k]) && !str2@.contains(result@[k])),
            forall|k: int| 0 <= k < i ==> (str2@.contains(str1@[k]) || result@.contains(str1@[k])),
    {
        let c = str1[i];
        proof {
            contains_lemma(str2, c);
        }
        if !is_char_in_vec(c, str2) {
            result.push(c);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}