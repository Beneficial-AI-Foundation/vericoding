// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int, k: int) -> bool {
    a >= 0 && b >= 0 && k >= 0
}

spec fn expected_takahashi_cookies(a: int, b: int, k: int) -> int
    recommends valid_input(a, b, k)
{
    if a >= k { a - k }
    else { 0 }
}

spec fn expected_aoki_cookies(a: int, b: int, k: int) -> int
    recommends valid_input(a, b, k)
{
    if a >= k { b }
    else if k - a < b { b - (k - a) }
    else { 0 }
}

spec fn correct_result(a: int, b: int, k: int, takahashi: int, aoki: int) -> bool
    recommends valid_input(a, b, k)
{
    takahashi == expected_takahashi_cookies(a, b, k) &&
    aoki == expected_aoki_cookies(a, b, k) &&
    takahashi >= 0 && aoki >= 0
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, k: int) -> (result: (int, int))
    requires valid_input(a, b, k)
    ensures correct_result(a, b, k, result.0, result.1)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}