// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    a > 1 && b >= 0
}

spec fn sockets_after_strips(strips: int, a: int) -> int
    recommends a > 1 && strips >= 0
{
    1 + strips * (a - 1)
}

spec fn ceiling_division(x: int, y: int) -> int
    recommends y > 0
{
    if x % y == 0 {
        x / y
    } else if x >= 0 {
        x / y + 1
    } else {
        x / y
    }
}

spec fn min_strips_needed(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if b <= 1 {
        0
    } else {
        ceiling_division(b - 1, a - 1)
    }
}

spec fn correct_result(a: int, b: int, result: int) -> bool
    recommends valid_input(a, b)
{
    result >= 0 &&
    sockets_after_strips(result, a) >= b &&
    (result == 0 || sockets_after_strips(result - 1, a) < b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no changes from previous turn */
proof fn lemma_ceiling_division_properties(x: int, y: int)
    requires
        x > 0,
        y > 0,
    ensures
        ceiling_division(x, y) * y >= x,
        (ceiling_division(x, y) - 1) * y < x,
        ceiling_division(x, y) > 0,
{
    let result = ceiling_division(x, y);

    if x % y == 0 {
        assert(result == x / y);
        assert(result * y == x);
        assert((result - 1) * y == x - y);
        assert(x - y < x);
    } else {
        assert(result == x / y + 1);
        assert(0 < x % y < y);

        assert(result * y == (x / y) * y + y);
        assert(result * y == x - (x % y) + y);
        assert(y - (x % y) > 0);
        assert(result * y > x);

        assert((result - 1) * y == (x / y) * y);
        assert((result - 1) * y == x - (x % y));
        assert((result - 1) * y < x);
    }

    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(x, y);
    assert(x / y >= 0);

    if x < y {
        assert(x / y == 0);
        assert(x % y == x && x > 0);
        assert(result == 1);
    }
    assert(result > 0);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures correct_result(a as int, b as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by using correct path to lemma_mul_le_mul */
{
    if b <= 1 {
        proof {
            assert(correct_result(a as int, b as int, 0));
        }
        return 0;
    }

    let needed = b as i32 - 1;
    let per_strip = a as i32 - 1;
    
    let result_val = if needed % per_strip == 0 {
        needed / per_strip
    } else {
        needed / per_strip + 1
    };

    proof {
        let a_int = a as int;
        let b_int = b as int;
        let result_int = result_val as int;

        let needed_int = b_int - 1;
        let per_strip_int = a_int - 1;
        assert(needed_int > 0 && per_strip_int > 0);
        
        vstd::arithmetic::div_mod::lemma_div_is_euclidean_for_i32(needed, per_strip);
        assert(result_int == ceiling_division(needed_int, per_strip_int));

        lemma_ceiling_division_properties(needed_int, per_strip_int);
        assert(correct_result(a_int, b_int, result_int));

        if result_int > i8::MAX as int {
            assert(result_int - 1 >= i8::MAX as int);
            vstd::arithmetic::lemmas::lemma_mul_le_mul(1, per_strip_int, i8::MAX as int, result_int - 1);
            
            assert(i8::MAX as int <= (result_int - 1) * per_strip_int);
            assert((result_int - 1) * per_strip_int < needed_int);
            assert(i8::MAX as int < needed_int);
            
            assert(b_int <= i8::MAX as int);
            assert(needed_int <= i8::MAX as int - 1);
            assert(false);
        }
        assert(result_val <= i8::MAX as i32);
        assert(result_val >= i8::MIN as i32);
    }
    
    result_val as i8
}
// </vc-code>


}

fn main() {}