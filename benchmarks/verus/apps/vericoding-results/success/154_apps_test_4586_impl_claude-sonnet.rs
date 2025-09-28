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
proof fn extract_digits_equiv(n: i32)
    requires
        1000 <= n <= 9999,
    ensures
        n / 1000 == (n as int) / 1000,
        (n / 100) % 10 == ((n as int) / 100) % 10,
        (n / 10) % 10 == ((n as int) / 10) % 10,
        n % 10 == (n as int) % 10,
{}

proof fn digit_bounds(n: int)
    requires
        1000 <= n <= 9999,
    ensures
        1 <= n / 1000 <= 9,
        0 <= (n / 100) % 10 <= 9,
        0 <= (n / 10) % 10 <= 9,
        0 <= n % 10 <= 9,
{}
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
    /* code modified by LLM (iteration 2): converted to i32 to fix integer literal overflow */
    let n32 = n as i32;
    let d1 = n32 / 1000;
    let d2 = (n32 / 100) % 10;
    let d3 = (n32 / 10) % 10;
    let d4 = n32 % 10;
    
    proof {
        extract_digits_equiv(n32);
        digit_bounds(n as int);
    }
    
    let first_three_same = d1 == d2 && d2 == d3;
    let last_three_same = d2 == d3 && d3 == d4;
    
    first_three_same || last_three_same
}
// </vc-code>


}

fn main() {}