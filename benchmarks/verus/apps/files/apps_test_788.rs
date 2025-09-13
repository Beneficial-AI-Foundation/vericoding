// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 7 && s[0] == 'A' && forall|i: int| 1 <= i < 7 ==> '0' <= s[i] <= '9'
}

spec fn digit_sum(s: Seq<char>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        (s[start] as int - '0' as int) + digit_sum(s, start + 1, end)
    }
}

spec fn zero_count(s: Seq<char>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        (if s[start] == '0' { 1 } else { 0 }) + zero_count(s, start + 1, end)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Seq<char>) -> (result: int)
    requires valid_input(s)
    ensures result == digit_sum(s, 1, 7) + 9 * zero_count(s, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}