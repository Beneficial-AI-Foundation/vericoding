// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 16
}

spec fn fact_truth_values() -> Seq<int> {
    seq![1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0]
}

spec fn valid_output(result: int) -> bool {
    result == 0 || result == 1
}

spec fn expected_output(n: int) -> int
    recommends valid_input(n)
{
    fact_truth_values()[n - 1]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        valid_output(result as int),
        result as int == expected_output(n as int)
// </vc-spec>
// <vc-code>
{
    let idx = (n as usize) - 1;
    let result = match idx {
        0 => 1i8,
        1 => 0i8,
        2 => 0i8,
        3 => 1i8,
        4 => 0i8,
        5 => 1i8,
        6 => 0i8,
        7 => 1i8,
        8 => 1i8,
        9 => 1i8,
        10 => 0i8,
        11 => 0i8,
        12 => 1i8,
        13 => 0i8,
        14 => 1i8,
        15 => 0i8,
        _ => 0i8,
    };
    result
}
// </vc-code>


}

fn main() {}