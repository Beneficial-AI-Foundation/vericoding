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
/* helper modified by LLM (iteration 5): corrected spec helper to_lowercase and cleaned_seq */
spec fn to_lowercase(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        match char::from_u32((c as u32) + 32) {
            Some(ch) => ch,
            None => c,
        }
    } else {
        c
    }
}

spec fn cleaned_seq(s: &str) -> Seq<char> {
    let chars_seq = s@;
    chars_seq.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c))
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
    /* code modified by LLM (iteration 5): build lowercase alnum vec using char::from_u32 */
    let mut v: Vec<char> = Vec::new();
    for ch in s.chars() {
        if ('a' <= ch && ch <= 'z') || ('A' <= ch && ch <= 'Z') || ('0' <= ch && ch <= '9') {
            let lc = if 'A' <= ch && ch <= 'Z' {
                match char::from_u32((ch as u32) + 32) {
                    Some(x) => x,
                    None => ch,
                }
            } else {
                ch
            };
            v.push(lc);
        }
    }
    let n = v.len();
    let mut i = 0usize;
    let mut ok = true;
    while i < n / 2
        invariant
            i <= n,
        decreases n - i
    {
        if v[i] != v[n - 1 - i] {
            ok = false;
            break;
        }
        i += 1;
    }
    ok
}
// </vc-code>

}
fn main() {}