// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple whitespace predicate */
spec fn is_whitespace(c: char) -> bool { c == ' ' || c == '\n' || c == '\t' || c == '\r' }
// </vc-helpers>

// <vc-spec>
fn reverse_words(words_str: &str) -> (result: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use vstd::string::String to avoid std allocation */
    let mut words: Vec<vstd::string::String> = Vec::new();
    let mut current: vstd::string::String = vstd::string::String::new();
    for c in words_str.chars() {
        if is_whitespace(c) {
            if !current.is_empty() {
                words.push(current.clone());
                current.clear();
            }
        } else {
            current.push(c);
        }
    }
    if !current.is_empty() {
        words.push(current);
    }
    let mut result: vstd::string::String = vstd::string::String::new();
    let mut first = true;
    let mut i: usize = words.len();
    while i > 0 {
        i -= 1;
        if !first {
            result.push(' ');
        }
        first = false;
        result.push_str(&words[i]);
    }
    result
}
// </vc-code>

}
fn main() {}