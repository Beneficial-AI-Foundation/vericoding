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
spec fn expected_len(n: int) -> nat { 3 }
// </vc-helpers>

// <vc-spec>
fn solve(n: i32) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures result@ == expected_result(n as int)
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    result.push('A');
    result.push('B');
    if n < 1000 {
        result.push('C');
    } else {
        result.push('D');
    }
    result
}
// </vc-code>


}

fn main() {}