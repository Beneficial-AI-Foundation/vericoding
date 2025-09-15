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
    let words: Vec<&str> = words_str.split(' ').collect();
    let reversed: Vec<&str> = words.into_iter().rev().collect();
    let result = reversed.join(" ");
    result
}
// </vc-code>

}
fn main() {}