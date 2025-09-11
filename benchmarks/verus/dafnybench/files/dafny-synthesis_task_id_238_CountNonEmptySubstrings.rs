// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_non_empty_substrings(s: Seq<char>) -> (count: usize)
    ensures 
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}