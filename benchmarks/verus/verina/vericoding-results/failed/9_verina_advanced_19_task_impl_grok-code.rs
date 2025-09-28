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
/* helper modified by LLM (iteration 4): Fixed char::from_u32 by replacing with direct (c as u32 + 32) as char cast, assuming the conversion is valid for ASCII uppercase letters */
fn is_upper_exec(c: char) -> bool { 'A' <= c && c <= 'Z' }

fn is_lower_exec(c: char) -> bool { 'a' <= c && c <= 'z' }

fn is_alpha_exec(c: char) -> bool { is_upper_exec(c) || is_lower_exec(c) }

fn to_lower_exec(c: char) -> char {
    if is_upper_exec(c) {
        ((c as u32) + 32) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn is_clean_palindrome(s: &str) -> (result: bool)
    ensures 
        result == (normalize_string(s) == normalize_string(s).reverse()),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Fixed compilation error by adding opening and closing braces */
    let mut norm_vec = Vec::new();
    for c in s.chars() {
        if is_alpha_exec(c) {
            let c_norm = to_lower_exec(c);
            norm_vec.push(c_norm);
        }
    }
    let len = norm_vec.len();
    for i in 0..(len / 2) {
        if norm_vec[i] != norm_vec[len - 1 - i] {
            return false;
        }
    }
    true
}
// </vc-code>

}
fn main() {}