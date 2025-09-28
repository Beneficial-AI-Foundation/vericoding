// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 1998
}

spec fn expected_result(n: int) -> Seq<char> {
    if n < 1000 { seq!['A', 'B', 'C'] } else { seq!['A', 'B', 'D'] }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i32) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures result@ == expected_result(n as int)
// </vc-spec>
// <vc-code>
{
    if n < 1000 {
        let mut result = Vec::new();
        result.push('A');
        result.push('B');
        result.push('C');
        proof {
            assert(result@ == seq!['A', 'B', 'C']);
        }
        result
    } else {
        let mut result = Vec::new();
        result.push('A');
        result.push('B');
        result.push('D');
        proof {
            assert(result@ == seq!['A', 'B', 'D']);
        }
        result
    }
}
// </vc-code>


}

fn main() {}