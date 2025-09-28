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
/* helper modified by LLM (iteration 5): restructured proof to avoid intermediate variables and use division properties directly */
fn ceiling_division_i8(x: i8, y: i8) -> (result: i8)
    requires
        x >= 0,
        y > 0,
        x <= 126,
    ensures
        result as int == ceiling_division(x as int, y as int),
{
    if x % y == 0 {
        x / y
    } else {
        x / y + 1
    }
}

/* helper modified by LLM (iteration 5): restructured proof to avoid intermediate variables and use division properties directly */
proof fn lemma_ceiling_division_properties(x: int, y: int)
    requires
        y > 0,
        x >= 0,
    ensures
        y * ceiling_division(x, y) >= x,
        if x > 0 {
            y * (ceiling_division(x, y) - 1) < x
        } else {
            true
        }
{
    if x % y == 0 {
        assert(ceiling_division(x, y) == x / y);
        assert(y * (x / y) == x);
        if x > 0 {
            assert(y * ((x / y) - 1) == x - y);
            assert(x - y < x);
        }
    } else {
        assert(ceiling_division(x, y) == x / y + 1);
        assert(y * (x / y + 1) == y * (x / y) + y);
        assert(y * (x / y) + y > x);
        if x > 0 {
            assert(y * (x / y) < x);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures correct_result(a as int, b as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use lemma to prove ceiling division properties */
    if b <= 1 {
        0
    } else {
        let x = b - 1;
        let y = a - 1;
        let strips = ceiling_division_i8(x, y);
        proof {
            // We have strips = ceiling_division(x as int, y as int)
            // Prove the properties of ceiling division for (x as int, y as int)
            lemma_ceiling_division_properties(x as int, y as int);
            
            // Now we know:
            //   y_int * strips_int >= x_int   [where y_int = y as int, strips_int = strips as int, x_int = x as int]
            //   and if x_int>0 then (y_int * (strips_int - 1)) < x_int

            // Condition 1: strips >= 0
            assert(strips >= 0); // because ceiling_division returns non-negative for non-negative inputs

            // Condition 2: sockets_after_strips(strips as int, a as int) >= b as int
            // sockets_after_strips(strips, a) = 1 + strips * (a-1)
            // We know: strips * (a-1) >= (b-1)   [by lemma: y_int * strips_int >= x_int, where y_int = a-1, x_int = b-1]
            // So 1 + strips * (a-1) >= 1 + (b-1) = b.
            assert(strips as int * (a as int - 1) >= (b as int - 1));
            assert(1 + strips as int * (a as int - 1) >= b as int);

            // Condition 3: if strips>0 then sockets_after_strips(strips-1, a) < b
            if strips > 0 {
                // Then we have: (a-1) * (strips-1) < (b-1)   [by lemma: since x_int = b-1 >= 1 (because b>1) so the second condition applies]
                assert((a as int - 1) * (strips as int - 1) < (b as int - 1));
                // Then sockets_after_strips(strips-1, a) = 1 + (strips-1)*(a-1) < 1 + (b-1) = b
                assert(1 + (a as int - 1) * (strips as int - 1) < b as int);
            }
        }
        strips
    }
}
// </vc-code>


}

fn main() {}