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
    /* code modified by LLM (iteration 5): fix syntax error in trigger annotation */
    let mut normalized = Vec::new();
    let s_len = s.unicode_len();
    
    let mut i: usize = 0;
    while i < s_len
        invariant
            i <= s_len,
            normalized@.len() <= i,
        decreases s_len - i
    {
        let c = s.get_char(i);
        if ('A' as char) <= c && c <= ('Z' as char) {
            normalized.push(c);
        } else if ('a' as char) <= c && c <= ('z' as char) {
            normalized.push(c);
        }
        i = i + 1;
    }
    
    let mut left: usize = 0;
    let mut right: usize = if normalized.len() > 0 { normalized.len() - 1 } else { 0 };
    let mut is_palindrome = true;
    
    while left < right
        invariant
            left <= right + 1,
            right < normalized.len() || (right == 0 && normalized.len() == 0),
            is_palindrome ==> forall|i: int| 0 <= i < left ==> #[trigger] normalized@[i] == normalized@[normalized@.len() - 1 - i],
        decreases right - left
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