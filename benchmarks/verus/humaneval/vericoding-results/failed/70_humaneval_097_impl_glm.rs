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
/* helper modified by LLM (iteration 5): fix safe unit digit to work with i8 inputs */
fn safe_unit_digit(n: i8) -> (result: i8)
    ensures
        result as int == unit_digit(n as int),
{
    let n_int = n as int;
    if n_int >= 0 {
        (n_int % 10 as int) as i8
    } else {
        ((-n_int) % 10 as int) as i8
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
    /* code modified by LLM (iteration 5): use fixed safe unit digit computation */
    let a_unit = safe_unit_digit(a);
    let b_unit = safe_unit_digit(b);
    
    proof {
        assert(a_unit as int == unit_digit(a as int));
        assert(b_unit as int == unit_digit(b as int));
        assert((a_unit as int) * (b_unit as int) == product_of_unit_digits(a as int, b as int));
        assert(valid_result((a_unit as int) * (b_unit as int)));
    }
    
    a_unit * b_unit
}
// </vc-code>


}

fn main() {}