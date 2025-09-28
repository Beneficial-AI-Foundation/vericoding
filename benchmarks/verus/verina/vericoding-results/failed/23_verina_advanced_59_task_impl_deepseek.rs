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
/* helper modified by LLM (iteration 5): Removed string_length helper and added ghost function for byte sequence conversion */
proof fn filter_map_alphanumeric_lower(s: Seq<char>) -> (cleaned: Seq<char>)
    ensures
        cleaned == s.filter(|c: char| is_alphanumeric(c)).map(|i, c: char| to_lowercase(c)),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let rest = filter_map_alphanumeric_lower(s.drop_last());
        let last_char = s[s.len() - 1];
        if is_alphanumeric(last_char) {
            rest.push(to_lowercase(last_char))
        } else {
            rest
        }
    }
}

proof fn seq_reverse_equals_self_implies_palindrome(s: Seq<char>) -> (b: bool)
    ensures
        b <==> (s == s.reverse()),
{
    if s == s.reverse() {
        true
    } else {
        false
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
/* code modified by LLM (iteration 5): Fixed compilation error by replacing direct as_bytes() call with char iteration */
{
    let chars: Vec<char> = s.chars().collect();
    let length = chars.len();
    let mut left: usize = 0;
    let mut right: usize = if length > 0 { length - 1 } else { 0 };
    
    while left <= right
        invariant
            left <= length,
            right < length,
            left <= right + 1,
    {
        let left_char = chars[left];
        let right_char = chars[right];
        
        if !is_alphanumeric(left_char) {
            left += 1;
        } else if !is_alphanumeric(right_char) {
            right -= 1;
        } else {
            if to_lowercase(left_char) != to_lowercase(right_char) {
                return false;
            }
            left += 1;
            if right > 0 {
                right -= 1;
            } else {
                break;
            }
        }
    }
    
    true
}
// </vc-code>

}
fn main() {}