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
/* helper modified by LLM (iteration 5): Fix `usize` type inference for indexing by casting `i` to `vstd::slice::SliceIndex` */
proof fn get_cleaned_chars(s: &str) -> (cleaned_chars: Vec<char>)
    ensures
        cleaned_chars@ == s@.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c)),
{
    let mut cleaned_chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            cleaned_chars@ == s@.subrange(0, i as int).filter(|c: char| is_alphanumeric(c)).map(|j, c: char| to_lowercase(c)),
            s.len() == (s@).len(), // Added for string length access
    {
        let c = s.as_bytes()[i as vstd::slice::SliceIndex] as char;
        if is_alphanumeric(c) {
            cleaned_chars.push(to_lowercase(c));
        }
        i = i + 1;
    }
    cleaned_chars
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
/* code modified by LLM (iteration 5): Add missing import `vstd::slice::SliceIndex` for `s.as_bytes()[i]` to fix `mismatched type` error */
{
    let cleaned_chars = get_cleaned_chars(s);

    let mut i: usize = 0;
    let mut j: usize = if cleaned_chars.len() == 0 { 0 } else { cleaned_chars.len() - 1 };

    while i < j
        invariant
            0 <= i && i <= cleaned_chars.len(),
            0 <= j && j < cleaned_chars.len(),
            i <= j + 1,
            // All characters from the beginning up to i match their counterparts from the end
            cleaned_chars@.subrange(0, i as int) == cleaned_chars@.subrange(j as int + 1, cleaned_chars.len() as int).reverse(),
    {
        if cleaned_chars[i] != cleaned_chars[j] {
            return false;
        }
        i = i + 1;
        j = j - 1;
    }
    true
}
// </vc-code>

}
fn main() {}