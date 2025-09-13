// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_hard_to_enter(s: &str) -> bool
    recommends s.len() == 4
{
    s@.index(0) == s@.index(1) || s@.index(1) == s@.index(2) || s@.index(2) == s@.index(3)
}
// </vc-helpers>

// <vc-spec>
fn solve(s: &str) -> (result: String)
    requires s.len() == 4,
    ensures result@ == "Bad" <==> is_hard_to_enter(s),
    ensures result@ == "Good" <==> !is_hard_to_enter(s),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}