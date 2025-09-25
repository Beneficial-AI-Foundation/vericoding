// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 0 && k >= 0 && k + 1 > 0
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool {
    result.len() == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

spec fn optimal_diplomas(n: int, k: int) -> int
    recommends valid_input(n, k)
{
    (n / 2) / (k + 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        valid_output(result@.map(|i, x| x as int), n as int, k as int) &&
        result@[0] as int == optimal_diplomas(n as int, k as int)
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