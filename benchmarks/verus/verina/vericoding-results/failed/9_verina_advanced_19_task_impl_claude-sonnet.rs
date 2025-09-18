// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_alpha(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

spec fn is_lower_alpha(c: char) -> bool {
    'a' <= c && c <= 'z'
}

spec fn is_alpha(c: char) -> bool {
    is_upper_alpha(c) || is_lower_alpha(c)
}

spec fn to_lower(c: char) -> char {
    if is_upper_alpha(c) {

        c
    } else {
        c
    }
}

spec fn normalize_char(c: char) -> Option<char> {
    if is_alpha(c) {
        Some(to_lower(c))
    } else {
        None
    }
}

spec fn normalize_string(s: &str) -> Seq<char> {
    s@.fold_left(Seq::empty(), |acc: Seq<char>, c: char|
        match normalize_char(c) {
            Some(c_norm) => acc.push(c_norm),
            None => acc,
        }
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type casting by using ghost variable for int index */
spec fn char_to_lower(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u8) + 32) as char
    } else {
        c
    }
}

fn normalize_char_exec(c: char) -> (result: Option<char>)
    ensures
        result == normalize_char(c),
{
    if ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') {
        if 'A' <= c && c <= 'Z' {
            Some(((c as u8) + 32) as char)
        } else {
            Some(c)
        }
    } else {
        None
    }
}

fn normalize_string_exec(s: &str) -> (result: Vec<char>)
    ensures
        result@ == normalize_string(s),
{
    let mut normalized = Vec::new();
    let mut i: usize = 0;
    
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            normalized@ == s@.subrange(0, i as int).fold_left(Seq::empty(), |acc: Seq<char>, c: char|
                match normalize_char(c) {
                    Some(c_norm) => acc.push(c_norm),
                    None => acc,
                }
            ),
    {
        proof {
            let ghost_i: int = i as int;
            let c = s@.index(ghost_i);
            
            if let Some(norm_c) = normalize_char_exec(c) {
                normalized.push(norm_c);
            }
        }
        
        i += 1;
    }
    
    normalized
}
// </vc-helpers>

// <vc-spec>
fn is_clean_palindrome(s: &str) -> (result: bool)
    ensures 
        result == (normalize_string(s) == normalize_string(s).reverse()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation using direct character comparison */
    let normalized = normalize_string_exec(s);
    let len = normalized.len();
    let mut left: usize = 0;
    let mut right: usize = len;
    
    while left < right
        invariant
            0 <= left <= right <= len,
            forall|k: int| 0 <= k < left ==> normalized@[k] == normalized@[(right as int) - 1 - k],
    {
        right -= 1;
        if normalized[left] != normalized[right] {
            return false;
        }
        left += 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}