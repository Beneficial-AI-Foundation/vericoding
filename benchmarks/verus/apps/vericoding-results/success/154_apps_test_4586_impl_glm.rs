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
/* helper modified by LLM (iteration 2): changed to use i8 and u16 arithmetic */
fn extract_digits_exec(n: i8) -> (i8, i8, i8, i8) {
    let n_u16 = n as u16;
    let d1 = (n_u16 / 1000) as i8;
    let r1 = n_u16 % 1000;
    let d2 = (r1 / 100) as i8;
    let r2 = r1 % 100;
    let d3 = (r2 / 10) as i8;
    let d4 = (r2 % 10) as i8;
    (d1, d2, d3, d4)
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
    /* code modified by LLM (iteration 2): use u16 arithmetic to avoid int type */
    let (d1, d2, d3, d4) = extract_digits_exec(n);
    let result = (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4);
    result
}
// </vc-code>


}

fn main() {}