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
/* helper modified by LLM (iteration 5): simplified proof structure for product bounds */
proof fn lemma_unit_digit_bounds(n: int)
    ensures unit_digit(n) >= 0 && unit_digit(n) <= 9
{
    let abs_n = if n >= 0 { n } else { -n };
    assert(abs_n >= 0);
    assert(abs_n % 10 >= 0 && abs_n % 10 <= 9);
}

proof fn lemma_product_bounds(a: int, b: int)
    ensures product_of_unit_digits(a, b) >= 0 && product_of_unit_digits(a, b) <= 81
{
    lemma_unit_digit_bounds(a);
    lemma_unit_digit_bounds(b);
    let ua = unit_digit(a);
    let ub = unit_digit(b);
    assert(ua >= 0 && ua <= 9);
    assert(ub >= 0 && ub <= 9);
    assert(ua * ub >= 0);
    assert(ua * ub <= 81);
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
    /* code modified by LLM (iteration 5): simplified implementation using direct conversion */
    let abs_a = if a >= 0 { a as u8 } else { 
        if a == i8::MIN { 128u8 } else { (-a) as u8 }
    };
    let abs_b = if b >= 0 { b as u8 } else {
        if b == i8::MIN { 128u8 } else { (-b) as u8 }
    };
    let unit_a = abs_a % 10;
    let unit_b = abs_b % 10;
    proof {
        lemma_product_bounds(a as int, b as int);
        assert(unit_a <= 9 && unit_b <= 9);
        assert(unit_a * unit_b <= 81);
        assert(81 <= 127);
        assert((unit_a * unit_b) as int <= 127);
    }
    let result = (unit_a * unit_b) as i8;
    result
}
// </vc-code>


}

fn main() {}