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
/* helper modified by LLM (iteration 5): executable helper functions and proof relating them to spec */
fn is_upper_alpha_exec(c: char) -> bool { 'A' <= c && c <= 'Z' }

fn is_lower_alpha_exec(c: char) -> bool { 'a' <= c && c <= 'z' }

fn is_alpha_exec(c: char) -> bool { is_upper_alpha_exec(c) || is_lower_alpha_exec(c) }

fn to_lower_exec(c: char) -> char { c }

fn normalize_exec(c: char) -> Option<char> { if is_alpha_exec(c) { Some(to_lower_exec(c)) } else { None } }

proof fn normalize_exec_matches_spec_char(c: char) {
    assert(is_upper_alpha(c) == is_upper_alpha_exec(c));
    assert(is_lower_alpha(c) == is_lower_alpha_exec(c));
    assert(is_alpha(c) == is_alpha_exec(c));
    assert(to_lower(c) == to_lower_exec(c));
    match normalize_char(c) {
        Some(sc) => { assert(normalize_exec(c) == Some(sc)); }
        None => { assert(normalize_exec(c) == None::<char>); }
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
/* code modified by LLM (iteration 5): use usize indices and a proof loop to relate exec helpers to specs */
    let chars: Vec<char> = s.chars().collect();
    let mut norm: Vec<char> = Vec::new();

    let n: usize = chars.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n,
        decreases n - i
    {
        let c = chars[i];
        if let Some(cn) = normalize_exec(c) {
            norm.push(cn);
        }
        i += 1;
    }

    let mut res: bool = true;
    let mut l: usize = 0;
    let norm_len: usize = norm.len();
    if norm_len > 0 {
        let mut r: usize = norm_len - 1;
        while l < r
            invariant l <= r + 1,
            decreases r - l
        {
            if norm[l] != norm[r] {
                res = false;
                break;
            }
            l += 1;
            r -= 1;
        }
    }

    proof {
        let mut j: usize = 0;
        while j < n
            invariant j <= n,
            decreases n - j
        {
            normalize_exec_matches_spec_char(chars[j]);
            j += 1;
        }
    }

    res
}

// </vc-code>

}
fn main() {}