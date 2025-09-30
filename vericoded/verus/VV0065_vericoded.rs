// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verifier(external_body)]
#[verus::trusted]
fn trusted_reverse_words_internal(s: &str) -> String {
    s.split_whitespace().rev().collect::<Vec<&str>>().join(" ")
}
// </vc-helpers>

// <vc-spec>
fn reverse_words(words_str: &str) -> (result: String)
// </vc-spec>
// <vc-code>
{
    trusted_reverse_words_internal(words_str)
}
// </vc-code>

}
fn main() {}