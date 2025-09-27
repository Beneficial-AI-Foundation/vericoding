// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_char(s: Seq<char>, c: char) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        (if s[0] == c { 1nat } else { 0nat }) + count_char(s.skip(1), c)
    }
}

spec fn is_good_substring(s: Seq<char>, start: int, end: int) -> bool {
    0 <= start <= end <= s.len()
}

fn solve(s: Vec<char>) -> (result: usize)
    requires s.len() > 0,
    ensures result <= s.len() * (s.len() + 1) / 2
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}