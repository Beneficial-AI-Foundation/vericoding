// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1000 <= n <= 9999
}

spec fn extract_digits(n: int) -> (int, int, int, int) {
    let d1 = n / 1000;
    let d2 = (n / 100) % 10;
    let d3 = (n / 10) % 10;
    let d4 = n % 10;
    (d1, d2, d3, d4)
}

spec fn is_good(n: int) -> bool {
    let (d1, d2, d3, d4) = extract_digits(n);
    (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple arithmetic facts for non-negative n */
proof fn digit_nonneg(n: int)
    requires
        0 <= n,
    ensures
        0 <= n / 1000,
        0 <= (n / 100) % 10,
        0 <= (n / 10) % 10,
        0 <= n % 10,
{
    assert(10 > 0);
    assert(100 > 0);
    assert(1000 > 0);
    assert(0 <= n / 1000);
    assert(0 <= n / 100);
    assert(0 <= n / 10);
    assert(0 <= n % 10 && n % 10 < 10);
    assert(0 <= (n / 10) % 10 && (n / 10) % 10 < 10);
    assert(0 <= (n / 100) % 10 && (n / 100) % 10 < 10);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: bool)
    requires 
        valid_input(n as int),
    ensures 
        result <==> is_good(n as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute the property using executable arithmetic only */
    let m: i32 = n as i32;
    let d1 = m / 1000;
    let d2 = (m / 100) % 10;
    let d3 = (m / 10) % 10;
    let d4 = m % 10;
    let result = (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4);
    result
}
// </vc-code>


}

fn main() {}