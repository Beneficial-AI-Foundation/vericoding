// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_hard_to_enter(s: Seq<char>) -> bool
    recommends s.len() == 4
{
    s[0] == s[1] || s[1] == s[2] || s[2] == s[3]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires s@.len() == 4
    ensures 
        result@.len() > 0,
        (result@ == seq!['B', 'a', 'd'] <==> is_hard_to_enter(s@)),
        (result@ == seq!['G', 'o', 'o', 'd'] <==> !is_hard_to_enter(s@))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}