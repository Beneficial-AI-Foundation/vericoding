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
/* helper modified by LLM (iteration 5): range of unit_digit */
proof fn unit_digit_range(n: int)
    ensures
        0 <= unit_digit(n),
        unit_digit(n) <= 9,
{
    let t = if n >= 0 { n } else { -n };
    assert(t >= 0);
    assert(unit_digit(n) == t % 10);
    assert(unit_digit(n) >= 0);
    assert(unit_digit(n) <= 9);
}

/* helper modified by LLM (iteration 5): product bounds for unit digits */
proof fn product_in_range(a: int, b: int)
    ensures
        0 <= product_of_unit_digits(a,b),
        product_of_unit_digits(a,b) <= 81,
{
    unit_digit_range(a);
    unit_digit_range(b);
    assert(product_of_unit_digits(a,b) == unit_digit(a) * unit_digit(b));
    assert(product_of_unit_digits(a,b) >= 0);
    assert(product_of_unit_digits(a,b) <= 81);
}

/* helper modified by LLM (iteration 5): cast roundtrip for i8 */
proof fn int_to_i8_roundtrip(n: int)
    requires
        -128 <= n,
        n <= 127,
    ensures
        (n as i8) as int == n,
{
    assert(((n as i8) as int) == n);
}

/* helper modified by LLM (iteration 5): relate i16 abs mod to spec unit_digit */
proof fn unit_digit_i16_eq(a: i8, aabs: i16)
    requires
        aabs == if (a as int) >= 0 { a as int } else { -(a as int) },
    ensures
        (aabs % 10) as int == unit_digit(a as int),
{
    assert(unit_digit(a as int) == ((if (a as int) >= 0 { a as int } else { -(a as int) }) % 10));
    assert((aabs % 10) as int == ((if (a as int) >= 0 { a as int } else { -(a as int) }) % 10));
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
  /* code modified by LLM (iteration 5): compute product using i16, prove relation to spec in proof block */
  let a_i16: i16 = a as i16;
  let b_i16: i16 = b as i16;
  let abs_a: i16 = if a_i16 >= 0 { a_i16 } else { -a_i16 };
  let abs_b: i16 = if b_i16 >= 0 { b_i16 } else { -b_i16 };
  let ua: i16 = abs_a % 10;
  let ub: i16 = abs_b % 10;
  let prod: i16 = ua * ub;

  proof {
    unit_digit_i16_eq(a, abs_a);
    unit_digit_i16_eq(b, abs_b);
    assert((ua as int) == unit_digit(a as int));
    assert((ub as int) == unit_digit(b as int));
    assert((prod as int) == unit_digit(a as int) * unit_digit(b as int));
    let prod_int: int = prod as int;
    product_in_range(a as int, b as int);
    int_to_i8_roundtrip(prod_int);
  }

  prod as i8
}

// </vc-code>


}

fn main() {}