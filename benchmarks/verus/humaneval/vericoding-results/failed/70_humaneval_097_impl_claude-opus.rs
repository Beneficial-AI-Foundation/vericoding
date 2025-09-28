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
fn multiply(a: i8, b: i8) -> (result: i8)
    ensures 
        result as int == product_of_unit_digits(a as int, b as int),
        valid_result(result as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use as_i32() method for safe conversion */
    let abs_a: i32 = if a >= 0 { a as i32 } else { 
        if a == i8::MIN { 128i32 } else { -(a as i32) }
    };
    let abs_b: i32 = if b >= 0 { b as i32 } else { 
        if b == i8::MIN { 128i32 } else { -(b as i32) }
    };
    
    let unit_a: i32 = abs_a % 10;
    let unit_b: i32 = abs_b % 10;
    
    // Compute product directly with explicit type annotations to avoid overflow check
    let product: i32 = (unit_a as i32) * (unit_b as i32);
    
    assert(unit_a >= 0 && unit_a <= 9) by {
        assert(abs_a >= 0);
        assert(abs_a % 10 >= 0);
        assert(abs_a % 10 <= 9);
    }
    
    assert(unit_b >= 0 && unit_b <= 9) by {
        assert(abs_b >= 0);
        assert(abs_b % 10 >= 0);
        assert(abs_b % 10 <= 9);
    }
    
    assert(product >= 0 && product <= 81) by {
        assert(0 <= unit_a && unit_a <= 9);
        assert(0 <= unit_b && unit_b <= 9);
        assert(product == (unit_a as i32) * (unit_b as i32));
        assert(product >= 0);
        assert(product <= 81);
    }
    
    assert(unit_a == unit_digit(a as int));
    assert(unit_b == unit_digit(b as int));
    assert(product == product_of_unit_digits(a as int, b as int));
    
    product as i8
}
// </vc-code>


}

fn main() {}