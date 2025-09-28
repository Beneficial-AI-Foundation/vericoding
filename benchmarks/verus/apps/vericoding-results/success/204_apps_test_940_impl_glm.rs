// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn is_triangle(a: int, b: int, c: int) -> bool {
    a + b > c && a + c > b && b + c > a
}

spec fn min_operations_needed(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let max_val = if a >= b && a >= c { a } else if b >= c { b } else { c };
    let sum_of_other_two = a + b + c - max_val;
    if max_val - sum_of_other_two + 1 > 0 { max_val - sum_of_other_two + 1 } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed boolean comparison in assertions */
proof fn triangle_condition_equivalence(a: int, b: int, c: int)
    requires valid_input(a, b, c)
    ensures is_triangle(a, b, c) <==> {
        let max_val = if a >= b && a >= c { a } else if b >= c { b } else { c };
        let sum_of_other_two = a + b + c - max_val;
        max_val < sum_of_other_two
    }
{
    let max_val = if a >= b && a >= c { a } else if b >= c { b } else { c };
    let sum_of_other_two = a + b + c - max_val;

    if a >= b && a >= c {
        assert(is_triangle(a, b, c) == (b + c > a));
        assert((b + c > a) == (a < b + c));
        assert((a < b + c) == (max_val < sum_of_other_two));
    } else if b >= c {
        assert(is_triangle(a, b, c) == (a + c > b));
        assert((a + c > b) == (b < a + c));
        assert((b < a + c) == (max_val < sum_of_other_two));
    } else {
        assert(is_triangle(a, b, c) == (a + b > c));
        assert((a + b > c) == (c < a + b));
        assert((c < a + b) == (max_val < sum_of_other_two));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        result >= 0,
        result as int == min_operations_needed(a as int, b as int, c as int),
        (result as int == 0) <==> is_triangle(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed integer overflow and ghost type usage */
{
    let max_val = if a >= b && a >= c { a } else if b >= c { b } else { c };
    let two_max_val = (max_val as i16) * 2;
    let total = (a as i16) + (b as i16) + (c as i16);
    let diff = two_max_val - total;
    let result = if diff >= 0 {
        (diff + 1) as i8
    } else {
        0
    };

    proof {
        let a_int = a as int;
        let b_int = b as int;
        let c_int = c as int;
        let max_val_int = max_val as int;
        let diff_int = 2 * max_val_int - (a_int + b_int + c_int);
        let spec_val = min_operations_needed(a_int, b_int, c_int);

        assert(diff_int == diff as int);
        assert(result as int == spec_val);

        triangle_condition_equivalence(a_int, b_int, c_int);
        assert((result as int == 0) <==> is_triangle(a_int, b_int, c_int));
    }

    result
}
// </vc-code>


}

fn main() {}