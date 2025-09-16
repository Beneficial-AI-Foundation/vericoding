// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (result:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): define executable vowel check function */
fn exec_is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

/* helper modified by LLM (iteration 4): fixed helper to use executable vowel check */
fn get_vowel_info(s: &str) -> (u32, Option<char>) {
    let mut count = 0;
    let mut last = None;
    for c in s.chars() {
        if exec_is_vowel(c) {
            count += 1;
        }
        last = Some(c);
    }
    (count, last)
}
// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)

    requires
        s@.len() <= u32::MAX,

    ensures
        inner_expr_vowels_count(s, ret),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): using corrected helper with executable vowel check */
{
    let (vowel_count, last_char) = get_vowel_info(s);
    let mut result = vowel_count;
    if let Some(c) = last_char {
        if c == 'y' || c == 'Y' {
            result += 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}