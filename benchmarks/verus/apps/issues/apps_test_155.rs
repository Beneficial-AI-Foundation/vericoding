// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, k: int) -> bool {
    n >= 2 && m >= 2 && n % 2 == 0 && k >= 0 && k < n * m
}

spec fn valid_output(result: &Vec<int>, n: int, m: int) -> bool {
    result.len() == 2 && result[0] >= 1 && result[0] <= n && result[1] >= 1 && result[1] <= m
}

spec fn correct_position(result: &Vec<int>, n: int, m: int, k: int) -> bool
    recommends valid_input(n, m, k) && result.len() == 2
{
    if k < n {
        result[0] == k + 1 && result[1] == 1
    } else {
        let k_remaining = k - n;
        let r = n - k_remaining / (m - 1);
        result[0] == r &&
        (r % 2 == 1 ==> result[1] == m - k_remaining % (m - 1)) &&
        (r % 2 == 0 ==> result[1] == 2 + k_remaining % (m - 1))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, k: i8) -> (result: Vec<i8>)
    requires
        valid_input(n as int, m as int, k as int)
    ensures
        result.len() == 2,
        {
            let spec_result: Vec<int> = result@.map(|i, x: i8| x as int);
            valid_output(&spec_result, n as int, m as int) && correct_position(&spec_result, n as int, m as int, k as int)
        }
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