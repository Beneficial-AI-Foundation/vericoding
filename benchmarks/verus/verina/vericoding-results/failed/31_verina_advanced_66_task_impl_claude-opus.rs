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
    let words: Vec<&str> = words_str.split_whitespace().collect();
    let mut reversed_words = Vec::new();
    let mut i = words.len();
    while i > 0 {
        i = i - 1;
        reversed_words.push(words[i]);
    }
    reversed_words.join(" ")
}
// </vc-code>

}
fn main() {}