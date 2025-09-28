// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn match_strings(s: &str, p: &str) -> (result: bool)
    requires s@.len() == p@.len(),
    ensures
        result == (forall|n: int| 0 <= n < s@.len() ==> 
            (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used StrSlice to access bytes via as_bytes */
    let s_slice: StrSlice = s.into();
    let p_slice: StrSlice = p.into();

    let s_bytes = s_slice.as_bytes();
    let p_bytes = p_slice.as_bytes();
    let len = s.len();
    let mut i: usize = 0;

    while i < len
        invariant
            s@.len() == p@.len(),
            len == s@.len(),
            0 <= i <= len,
            s_bytes@ == s@,
            p_bytes@ == p@,
            forall|n: int| 0 <= n < i ==> 
                (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8),
        decreases len - i
    {
        let s_char = s_bytes[i];
        let p_char = p_bytes[i];

        if s_char != p_char && p_char != ('?' as u8) {
            return false;
        }

        i = i + 1;
    }

    true
}
// </vc-code>

}
fn main() {}