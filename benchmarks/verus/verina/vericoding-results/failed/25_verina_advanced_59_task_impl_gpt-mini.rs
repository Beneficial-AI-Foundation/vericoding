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
/* helper modified by LLM (iteration 5): helpers to produce cleaned sequence of lowercase alphanumeric chars */
spec fn cleaned_chars(seq: Seq<char>) -> Seq<char> {
    seq.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c))
}

spec fn cleaned_from_str(s: &str) -> Seq<char> {
    cleaned_chars(s@)
}
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
{
    /* code modified by LLM (iteration 5): compute cleaned seq using spec helper and return equality with its reverse */
    let cleaned: Seq<char> = cleaned_from_str(s);
    let result: bool = cleaned == cleaned.reverse();
    result
}
// </vc-code>

}
fn main() {}