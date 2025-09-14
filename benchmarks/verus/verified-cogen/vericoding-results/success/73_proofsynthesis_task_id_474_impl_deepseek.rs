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
proof fn helper_lemma_replace_chars(str1: &Vec<char>, old_char: char, new_char: char, i: int) 
    requires 
        0 <= i < str1@.len(),
    ensures 
        inner_epxr_replace_chars(str1, old_char, new_char, i) == if str1[i] == old_char { new_char } else { str1[i] }
{
}

proof fn helper_decreases_lemma(n: nat) 
    ensures n >= 0
{
}
/* helper modified by LLM (iteration 2): Added decreases lemma for loop termination */
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
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let mut j: usize = 0;
    while j < str1.len()
        invariant 
            j <= str1.len(),
            result@.len() == j,
            forall|k: int| 0 <= k < j ==> result[k] == inner_epxr_replace_chars(str1, old_char, new_char, k),
        decreases str1.len() - j
    {
        proof { 
            helper_lemma_replace_chars(str1, old_char, new_char, j as int);
            helper_decreases_lemma((str1.len() - j) as nat);
        }
        let current_char = str1[j];
        let new_char_val = if current_char == old_char { new_char } else { current_char };
        result.push(new_char_val);
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}