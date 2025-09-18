// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_alphanumeric(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')
}

spec fn to_lowercase(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u32) + 32) as char
    } else {
        c
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed the lemma as not needed. */
// </vc-helpers>

// <vc-spec>
fn palindrome_ignore_non_alnum(s: &str) -> (result: bool)
    ensures 
        result <==> ({
            let chars_seq = s@;
            let cleaned = chars_seq.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c));
            let forward = cleaned;
            let backward = cleaned.reverse();
            forward == backward
        })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `filter_by` and `map` usage with direct spec functions, and used `ext_equal` for sequence comparison. */
{
    let chars_seq = s@;
    let cleaned: Seq<char> = chars_seq.filter(|c: char| is_alphanumeric(c)).map(|_i, c: char| to_lowercase(c));
    cleaned.ext_equal(cleaned.reverse())
}
// </vc-code>

}
fn main() {}