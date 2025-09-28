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
/* helper modified by LLM (iteration 5): [This helper is correct and remains unchanged from the previous iteration.] */
fn get_unit_digit(n: i8) -> (digit: i8)
    ensures
        digit as int == unit_digit(n as int),
        0 <= digit <= 9,
{
    // Widen to i16 to avoid overflow when taking absolute value of i8::MIN.
    let n_i16 = n as i16;
    let n_abs_i16 = if n_i16 >= 0 { n_i16 } else { -n_i16 };
    let digit_i16 = n_abs_i16 % 10;
    let digit = digit_i16 as i8;
    digit
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i8, b: i8) -> (result: i8)
    ensures 
        result as int == product_of_unit_digits(a as int, b as int),
        valid_result(result as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Added proof block to justify safe cast from i16 to i8.] */
{
    let unit_a = get_unit_digit(a);
    let unit_b = get_unit_digit(b);

    let product_i16 = (unit_a as i16) * (unit_b as i16);
    
    proof {
        assert(0 <= product_i16 <= 81);
    }

    let result = product_i16 as i8;
    result
}
// </vc-code>


}

fn main() {}