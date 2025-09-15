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
/* helper modified by LLM (iteration 3): added type annotations and fixed helper functions */
spec fn clean_and_lowercase(s: Seq<char>) -> Seq<char> {
    s.filter(|c: char| is_alphanumeric(c)).map(|i: int, c: char| to_lowercase(c))
}

proof fn char_bounds_lemma(c: char)
    ensures c as u32 <= 0x10FFFF
{
}

proof fn lowercase_preserves_alphanumeric(c: char)
    requires is_alphanumeric(c)
    ensures is_alphanumeric(to_lowercase(c))
{
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
    /* code modified by LLM (iteration 3): fixed type conversion and used ghost variables */
    let chars = s@;
    let cleaned = chars.filter(|c: char| is_alphanumeric(c)).map(|i: int, c: char| to_lowercase(c));
    
    let mut left = 0;
    let mut right: i32 = cleaned.len() as i32 - 1;
    
    while left < right
        invariant
            0 <= left <= cleaned.len(),
            -1 <= right < cleaned.len(),
            forall|k: int| 0 <= k < left ==> cleaned[k] == cleaned[right as int + 1 + k]
    {
        if cleaned[left] != cleaned[right as int] {
            return false;
        }
        left = left + 1;
        right = right - 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}