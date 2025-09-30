// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
proof fn i8_range_bounds(x: i8)
    ensures
        -128 <= x as int,
        x as int <= 127,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: (i8, i8))
    requires valid_input(a as int, b as int, k as int)
    ensures correct_result(a as int, b as int, k as int, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
{
    let tak: i8 = if a >= k { a - k } else { 0i8 };

    let rem: i8 = if a >= k { 0i8 } else { k - a };

    let aoki: i8 = if a >= k {
        b
    } else if rem < b {
        b - rem
    } else {
        0i8
    };

    (tak, aoki)
}
// </vc-code>


}

fn main() {}