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
proof fn unit_digit_nonnegative_lemma(n: int)
    ensures
        unit_digit(n) >= 0,
        unit_digit(n) < 10,
{
    /* helper modified by LLM (iteration 5): Added complete proof */
    assert(0 <= (if n >= 0 { n } else { -n }) % 10 && (if n >= 0 { n } else { -n }) % 10 < 10);
}

proof fn product_of_unit_digits_bound_lemma(a: int, b: int)
    ensures
        product_of_unit_digits(a, b) >= 0,
        product_of_unit_digits(a, b) <= 81,
{
    /* helper modified by LLM (iteration 5): Fixed upper bound assertion */
    unit_digit_nonnegative_lemma(a);
    unit_digit_nonnegative_lemma(b);
    assert(unit_digit(a) >= 0 && unit_digit(a) < 10);
    assert(unit_digit(b) >= 0 && unit_digit(b) < 10);
    assert(unit_digit(a) * unit_digit(b) >= 0);
    assert(unit_digit(a) * unit_digit(b) <= 9 * 9);
    assert(9 * 9 == 81);
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
    /* code modified by LLM (iteration 5): Removed unnecessary code and simplified implementation */
    let abs_a = if a >= 0 { a as i16 } else { -(a as i16) };
    let abs_b = if b >= 0 { b as i16 } else { -(b as i16) };
    let digit_a = (abs_a % 10) as i8;
    let digit_b = (abs_b % 10) as i8;
    let result = digit_a * digit_b;
    
    proof {
        product_of_unit_digits_bound_lemma(a as int, b as int);
        assert(valid_result(result as int));
        assert(result as int == product_of_unit_digits(a as int, b as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}