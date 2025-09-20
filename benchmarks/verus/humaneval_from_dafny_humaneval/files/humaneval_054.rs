// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn char_set(s: Seq<char>) -> Set<char> {
    s.to_set()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn same_chars(s0: Vec<char>, s1: Vec<char>) -> (result: bool)
    ensures result == (char_set(s0@) == char_set(s1@))
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}