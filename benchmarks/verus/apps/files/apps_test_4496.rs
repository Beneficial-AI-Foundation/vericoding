// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(d: int) -> bool {
    22 <= d <= 25
}

spec fn expected_output(d: int) -> Seq<char>
    recommends valid_input(d)
{
    let eve_count = 25 - d;
    let base_string = seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'];
    if eve_count == 0 {
        base_string
    } else {
        base_string + repeat_eve(eve_count)
    }
}

spec fn repeat_eve(count: int) -> Seq<char>
    recommends count >= 0
    decreases count
{
    if count == 0 {
        seq![]
    } else {
        seq![' ', 'E', 'v', 'e'] + repeat_eve(count - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(d: int) -> (result: String)
    requires valid_input(d)
    ensures result@ == expected_output(d)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}