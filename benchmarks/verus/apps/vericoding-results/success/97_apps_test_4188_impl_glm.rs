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
/* helper modified by LLM (iteration 2): replaced match with array lookup to avoid unreachable */
fn get_fact_value(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == expected_output(n as int)
{
    let table = [1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0];
    let index = (n - 1) as usize;
    table[index]
}
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
    /* code modified by LLM (iteration 2): no changes needed */
    let result = get_fact_value(n);
    result
}
// </vc-code>


}

fn main() {}