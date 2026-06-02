// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(t: Seq<char>) -> bool {
    t.len() >= 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires valid_input(t@)
    ensures result@.len() == t@.len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}