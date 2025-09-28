// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn unit_digit(n: int) -> int {
    (if n >= 0 { n } else { -n }) % 10
}

spec fn product_of_unit_digits(a: int, b: int) -> int {
    unit_digit(a) * unit_digit(b)
}

spec fn valid_result(result: int) -> bool {
    result >= 0 && result <= 81
}
// </vc-preamble>

// <vc-helpers>
fn exe_unit_digit(n: i32) -> (result: i32)
    ensures
        result as int == unit_digit(n as int),
{
    if n < 0 {
        - (n % 10)
    } else {
        n % 10
    }
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i8, b: i8) -> (result: i8)
    ensures 
        result as int == product_of_unit_digits(a as int, b as int),
        valid_result(result as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced abs() with manual abs computation for unit digits to avoid unsupported abs */
    let ua: i32 = exe_unit_digit(a as i32);
    let ub: i32 = exe_unit_digit(b as i32);
    let prod: i32 = ua * ub;
    #[verifier::truncate] (prod as i8)
}
// </vc-code>


}

fn main() {}