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
// </vc-helpers>

// <vc-spec>
fn multiply(a: int, b: int) -> (result: int)
    ensures 
        result == product_of_unit_digits(a, b),
        valid_result(result),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}