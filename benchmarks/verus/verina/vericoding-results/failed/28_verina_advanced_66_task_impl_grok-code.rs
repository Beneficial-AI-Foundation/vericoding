// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse_words(words_str: &str) -> (result: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): collected split words into Vec, then used into_iter().rev().collect() for reverse to avoid &mut method issue */
    let words: Vec<&str> = words_str.split_whitespace().collect();
    let reversed: Vec<&str> = words.into_iter().rev().collect();
    let result = reversed.join(" ");
    result
}
// </vc-code>

}
fn main() {}