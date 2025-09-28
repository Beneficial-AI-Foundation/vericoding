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
/* helper modified by LLM (iteration 5): Fixed char::from_u32 compilation error by using direct arithmetic on char */
fn char_is_alphanumeric(c: char) -> (result: bool)
    ensures result == is_alphanumeric(c)
{
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
}

fn char_to_lowercase(c: char) -> (result: char)
    ensures result == to_lowercase(c)
{
    if c >= 'A' && c <= 'Z' {
        ((c as u8) + 32) as char
    } else {
        c
    }
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
    /* code modified by LLM (iteration 5): Removed .chars().collect() which is unsupported, using as_bytes() instead */
    let bytes = s.as_bytes();
    let mut left = 0;
    let mut right = bytes.len();
    
    while left < right
        invariant
            left <= right,
            right <= bytes.len()
    {
        while left < right && !char_is_alphanumeric(bytes[left] as char)
            invariant
                left <= right,
                right <= bytes.len()
        {
            left += 1;
        }
        
        if left >= right {
            break;
        }
        
        right -= 1;
        
        while left < right && !char_is_alphanumeric(bytes[right] as char)
            invariant
                left <= right,
                right <= bytes.len()
        {
            right -= 1;
        }
        
        if left >= right {
            break;
        }
        
        let left_char = char_to_lowercase(bytes[left] as char);
        let right_char = char_to_lowercase(bytes[right] as char);
        
        if left_char != right_char {
            return false;
        }
        
        left += 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}