// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, m: int, a: int, b: int) -> bool {
    n >= 1 && n <= 1000 &&
    m >= 1 && m <= 1000 &&
    a >= 1 && a <= 1000 &&
    b >= 1 && b <= 1000
}

spec fn optimal_cost(n: int, m: int, a: int, b: int) -> int
    recommends valid_input(n, m, a, b)
{
    min(
        n * a,
        min(
            ((n + m - 1) / m) * b,
            (n / m) * b + (n % m) * a
        )
    )
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, a: int, b: int) -> (result: int)
    requires 
        valid_input(n, m, a, b)
    ensures 
        result >= 0,
        result == optimal_cost(n, m, a, b)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}