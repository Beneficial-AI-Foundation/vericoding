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
/* helper modified by LLM (iteration 5): fixed function syntax and removed ensures clause with compilation error */
spec fn char_to_lower(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u8) - ('A' as u8) + ('a' as u8)) as char
    } else {
        c
    }
}

fn normalize_and_collect(s: &str) -> (result: Vec<char>)
    requires s.is_ascii()
    ensures result@.len() <= s@.len()
{
    let mut normalized = Vec::new();
    let mut idx = 0;
    while idx < s.unicode_len()
        invariant 
            0 <= idx <= s.unicode_len(),
            normalized@.len() <= idx
    {
        let c = s.get_char(idx);
        if is_alpha(c) {
            let lower_c = char_to_lower(c);
            normalized.push(lower_c);
        }
        idx += 1;
    }
    normalized
}

fn is_palindrome_vec(v: &Vec<char>) -> (result: bool)
    ensures result == (v@ == v@.reverse())
{
    let len = v.len();
    let mut i = 0;
    while i < len / 2
        invariant 
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> v@[j] == v@[len - 1 - j]
    {
        if v[i] != v[len - 1 - i] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn is_clean_palindrome(s: &str) -> (result: bool)
    ensures 
        result == (normalize_string(s) == normalize_string(s).reverse()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using helper functions to implement palindrome check */
    let normalized = normalize_and_collect(s);
    is_palindrome_vec(&normalized)
}
// </vc-code>

}
fn main() {}