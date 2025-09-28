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
    /* code modified by LLM (iteration 2): [Use executable integer i16 for calculations to fix compile error] */
    let n_exec = n as i16;
    let d1 = n_exec / 1000;
    let d2 = (n_exec / 100) % 10;
    let d3 = (n_exec / 10) % 10;
    let d4 = n_exec % 10;
    (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4)
}
// </vc-code>


}

fn main() {}