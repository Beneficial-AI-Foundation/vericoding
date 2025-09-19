// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    exists|space_index: int| 0 <= space_index < input.len() && 
        input[space_index] == ' ' &&
    forall|i: int| 0 <= i < input.len() ==> 
        (input[i] == ' ' || ('0' <= input[i] <= '9'))
}

spec fn parse_two_ints(s: Seq<char>) -> (int, int) {
    if valid_input(s) { (1, 1) } else { (1, 1) }
}

spec fn lcm(a: int, b: int) -> int {
    if a > 0 && b > 0 { (a * b) / spec_gcd(a, b) } else { 1 }
}

spec fn spec_gcd(a: int, b: int) -> int
    decreases b
{
    if a > 0 && b > 0 {
        if b == 0 { a } else { spec_gcd(b, a % b) }
    } else { 1 }
}

spec fn valid_output(output: Seq<char>) -> bool {
    output.len() > 0 &&
    forall|i: int| 0 <= i < output.len() ==> #[trigger] output[i] >= '0' && #[trigger] output[i] <= '9'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures ({
        let nums = parse_two_ints(input@);
        let a = nums.0;
        let b = nums.1;
        a > 0 && b > 0
    }) && valid_output(result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}