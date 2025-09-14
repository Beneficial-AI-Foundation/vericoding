// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int) -> bool {
    n >= 2 && m >= 1 && n <= m && m <= 200000
}

spec fn combination(n: int, k: int, modulus: int) -> int {
    0  /* placeholder - actual combinatorial calculation */
}

spec fn power(base: int, exp: int, modulus: int) -> int {
    0  /* placeholder - actual modular exponentiation */
}

spec fn expected_result(n: int, m: int) -> int {
    if n == 2 {
        0
    } else {
        (((combination(m, n - 1, 998244353) * (n - 2)) % 998244353) * power(2, n - 3, 998244353)) % 998244353
    }
}

spec fn valid_output(result: int) -> bool {
    0 <= result < 998244353
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int) -> (result: int)
    requires 
        valid_input(n, m)
    ensures 
        valid_output(result),
        result == expected_result(n, m)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}