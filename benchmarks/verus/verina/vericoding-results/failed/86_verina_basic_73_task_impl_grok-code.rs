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
    if s.len() != p.len() {
        return false;
    }
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall |j| 0 <= j < i ==> (s@[j] == p@[j] || p@[j] == '?' as u8),
        decreases (s.len() - i),
    {
        if s.as_bytes()[i as usize] != p.as_bytes()[i as usize] && p.as_bytes()[i as usize] != b'?' {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}