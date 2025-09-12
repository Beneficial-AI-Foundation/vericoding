// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: int) -> bool {
    1 <= n <= 100 && 0 <= a <= n * n
}

spec fn black_squares(n: int, a: int) -> int
    recommends valid_input(n, a)
{
    n * n - a
}

spec fn valid_output(n: int, a: int, result: int) -> bool
    recommends valid_input(n, a)
{
    result == black_squares(n, a) && result >= 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn calculate_black_squares(n: int, a: int) -> (black_squares: int)
    requires valid_input(n, a)
    ensures valid_output(n, a, black_squares)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}