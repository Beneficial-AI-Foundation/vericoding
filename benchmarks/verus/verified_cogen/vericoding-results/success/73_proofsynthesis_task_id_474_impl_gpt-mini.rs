// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn inner_epxr_replace_chars(str1: &Vec<char>, old_char: char, new_char: char, i: int) -> (result: char) {
    if str1[i] == old_char {
        new_char
    } else {
        str1[i]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): correctness predicate for replace_chars */
spec fn replace_chars_correct(str1: &Vec<char>, old_char: char, new_char: char, result: &Vec<char>) -> bool {
    str1@.len() == result@.len() &&
    forall|i: int|
        0 <= i < str1.len() ==> result[i] == inner_epxr_replace_chars(str1, old_char, new_char, i)
}
// </vc-helpers>

// <vc-spec>
fn replace_chars(str1: &Vec<char>, old_char: char, new_char: char) -> (result: Vec<char>)

    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == inner_epxr_replace_chars(str1, old_char, new_char, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use usize loop index, maintain invariants with casts */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            0 <= (i as int) && (i as int) <= (str1.len() as int),
            result@.len() == (i as int),
            forall|j: int|
                0 <= j < (i as int) ==> result[j] == inner_epxr_replace_chars(str1, old_char, new_char, j),
        decreases
            (str1.len() - i)
    {
        let c: char;
        let ch: char = str1[i];
        if ch == old_char {
            c = new_char;
        } else {
            c = ch;
        }
        result.push(c);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}