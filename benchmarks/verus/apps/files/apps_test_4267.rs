// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_temperature(temp: int) -> bool {
    -40 <= temp <= 40
}

spec fn expected_output(temp: int) -> Seq<char> {
    if temp >= 30 { seq!['Y', 'e', 's', '\n'] } else { seq!['N', 'o', '\n'] }
}

spec fn correct_output(temp: int, output: Seq<char>) -> bool {
    output == expected_output(temp)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: Vec<u8>)
    requires valid_temperature(x as int)
    ensures correct_output(x as int, result@.map(|i: int, b: u8| b as char))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}

fn main() {}