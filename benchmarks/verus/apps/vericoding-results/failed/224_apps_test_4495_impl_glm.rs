// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, x: int) -> bool {
    a >= 0 && b >= a && x > 0
}

spec fn count_divisible_in_range(a: int, b: int, x: int) -> int
    recommends valid_input(a, b, x)
{
    if a == 0 {
        b / x + 1
    } else {
        b / x - (a - 1) / x
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_divisible(a: i8, b: i8, x: i8) -> (count: i8)
    requires 
        valid_input(a as int, b as int, x as int),
    ensures 
        count as int == count_divisible_in_range(a as int, b as int, x as int),
        count >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed int usage and added proof block */
    let count;
    if a == 0 {
        count = (b / x) + 1;
    } else {
        count = (b / x) - ((a - 1) / x);
    }
    proof {
        let a_int = a as int;
        let b_int = b as int;
        let x_int = x as int;
        if a == 0 {
            assert(count_divisible_in_range(a_int, b_int, x_int) == b_int / x_int + 1);
            assert(count as int == b_int / x_int + 1);
        } else {
            assert(count_divisible_in_range(a_int, b_int, x_int) == b_int / x_int - (a_int - 1) / x_int);
            assert(count as int == b_int / x_int - (a_int - 1) / x_int);
        }
        assert(count >= 0);
    }
    count
}
// </vc-code>


}

fn main() {}