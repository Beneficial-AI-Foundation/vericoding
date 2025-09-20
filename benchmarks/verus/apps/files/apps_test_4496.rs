// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(d: int) -> bool {
    22 <= d <= 25
}

spec fn expected_output(d: int) -> Seq<char> {
    if valid_input(d) {
        let eve_count = 25 - d;
        let base_string = seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'];
        if eve_count == 0 {
            base_string
        } else {
            base_string + repeat_eve(eve_count)
        }
    } else {
        seq![]
    }
}

spec fn repeat_eve(count: int) -> Seq<char>
    decreases count
{
    if count <= 0 {
        seq![]
    } else {
        seq![' ', 'E', 'v', 'e'] + repeat_eve(count - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(d: i8) -> (result: String)
    requires valid_input(d as int)
    ensures result@ == expected_output(d as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}