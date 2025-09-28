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
/* helper modified by LLM (iteration 5): Using direct char arithmetic without from_u32 */
fn is_alnum(c: char) -> (result: bool)
    ensures result == is_alphanumeric(c)
{
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
}

fn to_lower(c: char) -> (result: char)
    ensures result == to_lowercase(c)
{
    if c >= 'A' && c <= 'Z' {
        // Direct character mapping for uppercase to lowercase
        if c == 'A' { 'a' }
        else if c == 'B' { 'b' }
        else if c == 'C' { 'c' }
        else if c == 'D' { 'd' }
        else if c == 'E' { 'e' }
        else if c == 'F' { 'f' }
        else if c == 'G' { 'g' }
        else if c == 'H' { 'h' }
        else if c == 'I' { 'i' }
        else if c == 'J' { 'j' }
        else if c == 'K' { 'k' }
        else if c == 'L' { 'l' }
        else if c == 'M' { 'm' }
        else if c == 'N' { 'n' }
        else if c == 'O' { 'o' }
        else if c == 'P' { 'p' }
        else if c == 'Q' { 'q' }
        else if c == 'R' { 'r' }
        else if c == 'S' { 's' }
        else if c == 'T' { 't' }
        else if c == 'U' { 'u' }
        else if c == 'V' { 'v' }
        else if c == 'W' { 'w' }
        else if c == 'X' { 'x' }
        else if c == 'Y' { 'y' }
        else if c == 'Z' { 'z' }
        else { c }
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
    /* code modified by LLM (iteration 5): Two-pointer palindrome check with proper str length handling */
    let len = s.len();
    if len == 0 {
        return true;
    }
    
    let mut left: usize = 0;
    let mut right: usize = len - 1;
    
    while left < right
        invariant
            left <= len,
            right < len,
            forall|i: int, j: int| 0 <= i < left && right < j < len ==>
                (!is_alphanumeric(s@[i]) || !is_alphanumeric(s@[j]) ||
                 to_lowercase(s@[i]) == to_lowercase(s@[j]))
    {
        let left_char = s.get_char(left);
        let right_char = s.get_char(right);
        
        if !is_alnum(left_char) {
            left = left + 1;
        } else if !is_alnum(right_char) {
            if right > 0 {
                right = right - 1;
            } else {
                break;
            }
        } else {
            if to_lower(left_char) != to_lower(right_char) {
                return false;
            }
            left = left + 1;
            if right > 0 {
                right = right - 1;
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