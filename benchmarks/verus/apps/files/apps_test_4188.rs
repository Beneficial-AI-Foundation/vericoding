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
fn solve(n: int) -> (result: int)
    requires 
        valid_input(n)
    ensures 
        valid_output(result),
        result == expected_output(n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}