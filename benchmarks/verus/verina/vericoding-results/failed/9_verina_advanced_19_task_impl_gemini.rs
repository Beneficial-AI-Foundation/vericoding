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
/* helper modified by LLM (iteration 5): fixed compilation error by using &str slice syntax */
fn exec_normalize_string(s: &str) -> (result: Vec<char>)
    ensures result@ == normalize_string(s)
{
    let mut vec = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.is_char_boundary(i),
            vec@ == normalize_string(&s[0..i]),
    {
        let (c, next_i) = s.get_char(i);
        if ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') {
            vec.push(c);
        }
        i = next_i;
    }
    vec
}

/* helper modified by LLM (iteration 5): no changes from previous correct version */
fn exec_is_palindrome(v: &Vec<char>) -> (result: bool)
    ensures result == (v@ == v@.reverse()),
{
    let len = v.len();
    if len <= 1 {
        return true;
    }
    let mut i: usize = 0;
    let mut j: usize = len - 1;
    
    while i < j
        invariant
            len == v.len(),
            0 <= i, j < len,
            i + j == len - 1,
            forall|k: int| 0 <= k < i as int ==> v[k] == v[len - 1 - k],
        decreases (j - i) as nat,
    {
        if v[i] != v[j] {
            proof {
                let k = i as int;
                assert(v@.reverse()[k] == v[len - 1 - k]);
                assert(j as int == len - 1 - k);
                assert(v@.reverse()[k] == v[j as int]);
                assert(v@[k] != v@.reverse()[k]);
            }
            return false;
        }
        i = i + 1;
        j = j - 1;
    }

    proof {
        assert(v@ == v@.reverse());
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
    /* code modified by LLM (iteration 5): No changes needed, logic is correct. */
    let normalized_vec = exec_normalize_string(s);
    exec_is_palindrome(&normalized_vec)
}
// </vc-code>

}
fn main() {}