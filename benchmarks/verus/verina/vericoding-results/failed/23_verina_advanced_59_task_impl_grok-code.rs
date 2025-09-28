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
/* helper modified by LLM (iteration 3): No helpers needed */
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
    /* code modified by LLM (iteration 4): Fixed unsupported pattern in invariant by replacing placeholder with index variable */
    let tracked chars_seq = s@;
    let chars: Vec<char> = s.chars().collect();
    let mut cleaned = Vec::new();
    let mut i: usize = 0;
    while i < chars.len()
        invariant
            i as int <= chars@.len() as int,
            cleaned@ == chars@.subrange(0, i as int).filter(|c| is_alphanumeric(c)).map(|i, c| to_lowercase(c)),
        decreases chars.len() - i
    {
        if is_alphanumeric(chars[i]) {
            cleaned.push(to_lowercase(chars[i]));
        }
        i += 1;
    }
    let len: usize = cleaned.len();
    let mut k: usize = 0;
    let mut is_pal = true;
    while k < len / 2
        invariant
            k as int <= (len / 2) as int,
            is_pal == (forall |m: int| 0 <= m < k as int ==> cleaned@[m as int] == cleaned@[(len as int) - 1 - m as int]),
        decreases len / 2 - k
    {
        if cleaned[k] != cleaned[len - 1 - k] {
            is_pal = false;
            break;
        } else {
            k += 1;
        }
    }
    is_pal
}
// </vc-code>

}
fn main() {}