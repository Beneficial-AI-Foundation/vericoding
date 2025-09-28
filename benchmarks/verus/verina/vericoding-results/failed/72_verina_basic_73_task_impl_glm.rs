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
    let n = s.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> 
                (s@.index(j) == p@.index(j) || p@.index(j) == '?' as u8)
        decreases n - i
    {
        let s_byte = s.as_bytes()[i];
        let p_byte = p.as_bytes()[i];
        if s_byte != p_byte && p_byte != b'?' {
            return false;
        }
        i += 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}