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
/* helper modified by LLM (iteration 5): trivial lemma preserved for verification */
proof fn triv_lemma() ensures true {
}

// </vc-helpers>

// <vc-spec>
fn is_clean_palindrome(s: &str) -> (result: bool)
    ensures 
        result == (normalize_string(s) == normalize_string(s).reverse()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build reversed sequence and compare without using Seq.reverse() */
    let seq: Seq<char> = normalize_string(s);
    let n: nat = seq.len();
    let mut rev: Seq<char> = Seq::empty();
    let mut k: nat = n;
    while k > 0
        invariant
            rev.len() + k == n,
            (forall |j: nat| j < rev.len() ==> rev@[j] == seq@[n - 1u64 - j]),
        decreases k
    {
        k = k - 1u64;
        rev = rev.push(seq@[k]);
    }
    seq == rev
}
// </vc-code>

}
fn main() {}