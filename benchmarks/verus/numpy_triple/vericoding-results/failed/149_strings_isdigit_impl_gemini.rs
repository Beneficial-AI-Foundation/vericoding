// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added spec function body and rewrote check_all_digits to use usize for clean indexing */
spec fn all_chars_digit(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] && s[i] <= '9'
}

fn check_all_digits(s: &String) -> (result: bool)
    ensures result == all_chars_digit(s@)
{
    let s_view = s@;
    let mut i: usize = 0;
    while i < s_view.len()
        invariant
            s@ == s_view,
            forall|k: int| 0 <= k < i as int ==> '0' <= s_view@[k] && s_view@[k] <= '9'
    {
        let c = s_view@[i as int];
        if !('0' <= c && c <= '9') {
            proof {
                assert(!all_chars_digit(s@));
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(all_chars_digit(s@));
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i]@.len() > 0 && all_chars_digit(a[i]@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): removed problematic invariant and fixed types in loop invariant */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == (a[j]@.len() > 0 && all_chars_digit(a[j]@))
    {
        let s = &a[i];
        let val = s.len() > 0 && check_all_digits(s);
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}