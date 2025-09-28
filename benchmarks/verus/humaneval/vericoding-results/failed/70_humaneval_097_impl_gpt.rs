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
proof fn lemma_unit_digit_bounds(n: int)
    ensures
        0 <= unit_digit(n),
        unit_digit(n) <= 9,
{
    if n >= 0 {
        assert(unit_digit(n) == n % 10);
        assert(0 <= n % 10);
        assert(n % 10 < 10);
        assert(0 <= unit_digit(n));
        assert(unit_digit(n) < 10);
    } else {
        assert(unit_digit(n) == (-n) % 10);
        assert(0 <= (-n) % 10);
        assert(((-n) % 10) < 10);
        assert(0 <= unit_digit(n));
        assert(unit_digit(n) < 10);
    }
    assert(unit_digit(n) <= 9);
}

proof fn lemma_product_of_unit_digits_bounds(a: int, b: int)
    ensures
        0 <= product_of_unit_digits(a, b),
        product_of_unit_digits(a, b) <= 81,
{
    lemma_unit_digit_bounds(a);
    lemma_unit_digit_bounds(b);
    assert(0 <= unit_digit(a));
    assert(unit_digit(a) <= 9);
    assert(0 <= unit_digit(b));
    assert(unit_digit(b) <= 9);
    assert(0 <= unit_digit(a) * unit_digit(b));
    assert(unit_digit(a) * unit_digit(b) <= 9 * unit_digit(b));
    assert(9 * unit_digit(b) <= 9 * 9);
    assert(product_of_unit_digits(a, b) == unit_digit(a) * unit_digit(b));
    assert(product_of_unit_digits(a, b) <= 81);
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
    let a_int = a as int;
    let b_int = b as int;

    let abs_a = if a_int >= 0 { a_int } else { -a_int };
    let abs_b = if b_int >= 0 { b_int } else { -b_int };

    let ud_a = abs_a % 10;
    let ud_b = abs_b % 10;

    proof {
        if a_int >= 0 {
            assert(unit_digit(a_int) == a_int % 10);
            assert(ud_a == unit_digit(a_int));
        } else {
            assert(unit_digit(a_int) == (-a_int) % 10);
            assert(ud_a == unit_digit(a_int));
        }
        if b_int >= 0 {
            assert(unit_digit(b_int) == b_int % 10);
            assert(ud_b == unit_digit(b_int));
        } else {
            assert(unit_digit(b_int) == (-b_int) % 10);
            assert(ud_b == unit_digit(b_int));
        }
    }

    let prod = ud_a * ud_b;

    proof {
        assert(0 <= ud_a);
        assert(ud_a < 10);
        assert(0 <= ud_b);
        assert(ud_b < 10);
        assert(ud_a <= 9);
        assert(ud_b <= 9);
        assert(0 <= prod);
        assert(prod <= 9 * ud_b);
        assert(9 * ud_b <= 9 * 9);
        assert(prod <= 81);
    }

    assert(-128 <= prod);
    assert(prod <= 127);
    let result = prod as i8;

    proof {
        assert(prod == ud_a * ud_b);
        assert(ud_a == unit_digit(a_int));
        assert(ud_b == unit_digit(b_int));
        assert(prod == unit_digit(a_int) * unit_digit(b_int));
        assert(product_of_unit_digits(a_int, b_int) == unit_digit(a_int) * unit_digit(b_int));
        assert(prod == product_of_unit_digits(a_int, b_int));
        assert(result as int == prod);
        assert(0 <= result as int);
        assert(result as int <= 81);
    }

    result
}
// </vc-code>


}

fn main() {}