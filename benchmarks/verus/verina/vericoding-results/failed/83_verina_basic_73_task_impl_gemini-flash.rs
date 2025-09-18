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
/* code modified by LLM (iteration 5): The error indicated `index` calls cannot use `int` in non-ghost contexts, so I cast to `usize` instead for consistent types with the loop variable `i`. */
{
    let len: usize = s.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i && i <= len,
            forall|n: int| 0 <= n && n < i ==> (s@.index(n) == p@.index(n) || p@.index(n) == (b'?' as_u8())),
        decreases len - i
    {
        if s@.index(i as int) != p@.index(i as int) && p@.index(i as int) != (b'?' as_u8()) {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}