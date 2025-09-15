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
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            s@.len() == p@.len(),
            forall|n: int| 0 <= n < i ==> (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8),
    {
        if s.get_char(i) != p.get_char(i) && p.get_char(i) != '?' {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}