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

// </vc-helpers>

// <vc-spec>
fn is_clean_palindrome(s: &str) -> (result: bool)
    ensures 
        result == (normalize_string(s) == normalize_string(s).reverse()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid unsupported s.len() by using index-based iteration */
    let mut normalized = Vec::new();
    let mut i: usize = 0;
    
    // Build normalized string by iterating until we can't get more characters
    loop
        invariant
            0 <= i,
            normalized@.len() <= i,
    {
        // Try to get character at index i
        if i >= 1000000 {  // Reasonable upper bound to ensure termination
            break;
        }
        
        match s.get_char_opt(i) {
            None => break,  // End of string reached
            Some(c) => {
                if ('A' as char <= c && c <= 'Z' as char) || ('a' as char <= c && c <= 'z' as char) {
                    let c_lower = if 'A' as char <= c && c <= 'Z' as char {
                        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
                    } else {
                        c
                    };
                    normalized.push(c_lower);
                }
                i = i + 1;
            }
        }
    }
    
    // Check if normalized string is a palindrome
    let mut left: usize = 0;
    let mut right: usize = if normalized.len() > 0 { normalized.len() - 1 } else { 0 };
    let mut is_palindrome = true;
    
    while left < right
        invariant
            0 <= left <= normalized.len(),
            0 <= right < normalized.len(),
            left <= right + 1,
    {
        if normalized[left] != normalized[right] {
            is_palindrome = false;
            break;
        }
        left = left + 1;
        if right > 0 {
            right = right - 1;
        } else {
            break;
        }
    }
    
    is_palindrome
}
// </vc-code>

}
fn main() {}