// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_rating(r: int) -> bool {
    0 <= r <= 4208
}

spec fn contest_for_rating(r: int) -> Seq<char> {
    if r < 1200 {
        seq!['A', 'B', 'C', '\n']
    } else if r < 2800 {
        seq!['A', 'R', 'C', '\n']
    } else {
        seq!['A', 'G', 'C', '\n']
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(r: int) -> (result: Seq<char>)
    requires 
        valid_rating(r)
    ensures 
        result == contest_for_rating(r),
        r < 1200 ==> result == seq!['A', 'B', 'C', '\n'],
        1200 <= r < 2800 ==> result == seq!['A', 'R', 'C', '\n'],
        r >= 2800 ==> result == seq!['A', 'G', 'C', '\n']
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}