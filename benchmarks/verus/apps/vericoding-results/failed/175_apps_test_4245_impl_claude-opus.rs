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
/* helper modified by LLM (iteration 5): Fixed assertions using Verus built-in properties and more explicit proof steps */
proof fn ceiling_division_properties(x: int, y: int)
    requires y > 0
    ensures
        ceiling_division(x, y) * y >= x,
        x >= 0 ==> ceiling_division(x, y) >= 0,
        x % y == 0 ==> ceiling_division(x, y) == x / y,
        x % y != 0 && x >= 0 ==> ceiling_division(x, y) == x / y + 1
{
    // Verus knows Euclidean division property
    // x == (x / y) * y + (x % y) is built-in
    
    if x % y == 0 {
        assert(ceiling_division(x, y) == x / y);
        assert(x % y == 0);
        assert(ceiling_division(x, y) * y == (x / y) * y);
        assert(ceiling_division(x, y) * y == x);
    } else if x >= 0 {
        assert(ceiling_division(x, y) == x / y + 1);
        assert(0 < x % y && x % y < y);
        assert(ceiling_division(x, y) * y == (x / y + 1) * y);
        // Use distributive property explicitly
        assert((x / y + 1) * y == (x / y) * y + 1 * y);
        assert((x / y + 1) * y == (x / y) * y + y);
        // Since x == (x / y) * y + (x % y) and 0 < x % y < y
        assert((x / y) * y + y > (x / y) * y + (x % y));
        assert((x / y) * y + y > x);
        assert(ceiling_division(x, y) * y >= x);
    }
}

proof fn sockets_formula_proof(strips: int, a: int)
    requires
        a > 1,
        strips >= 0
    ensures
        sockets_after_strips(strips, a) == 1 + strips * (a - 1),
        strips > 0 ==> sockets_after_strips(strips, a) > sockets_after_strips(strips - 1, a)
{
    if strips > 0 {
        assert(sockets_after_strips(strips, a) == 1 + strips * (a - 1));
        assert(sockets_after_strips(strips - 1, a) == 1 + (strips - 1) * (a - 1));
        // Use distributive property explicitly
        assert(strips * (a - 1) == (strips - 1 + 1) * (a - 1));
        assert((strips - 1 + 1) * (a - 1) == (strips - 1) * (a - 1) + 1 * (a - 1));
        assert(strips * (a - 1) == (strips - 1) * (a - 1) + (a - 1));
        assert(strips * (a - 1) - (strips - 1) * (a - 1) == (a - 1));
    }
}

proof fn min_strips_correctness(a: int, b: int, result: int)
    requires
        valid_input(a, b),
        result == min_strips_needed(a, b)
    ensures
        correct_result(a, b, result)
{
    if b <= 1 {
        assert(result == 0);
        assert(sockets_after_strips(0, a) == 1);
        assert(sockets_after_strips(0, a) >= b);
    } else {
        assert(result == ceiling_division(b - 1, a - 1));
        ceiling_division_properties(b - 1, a - 1);
        assert(result * (a - 1) >= b - 1);
        assert(sockets_after_strips(result, a) == 1 + result * (a - 1));
        assert(sockets_after_strips(result, a) >= b);
        
        if result > 0 {
            // Need to prove that sockets_after_strips(result - 1, a) < b
            if (b - 1) % (a - 1) == 0 {
                assert(result == (b - 1) / (a - 1));
                // When remainder is 0: b - 1 == result * (a - 1)
                // Verus knows: (b - 1) == ((b - 1) / (a - 1)) * (a - 1) + 0
                assert((b - 1) % (a - 1) == 0);
                assert((b - 1) == ((b - 1) / (a - 1)) * (a - 1));
                assert(result == (b - 1) / (a - 1));
                assert((b - 1) == result * (a - 1));
                // So (result - 1) * (a - 1) == b - 1 - (a - 1)
                assert((result - 1) * (a - 1) == result * (a - 1) - (a - 1));
                assert((result - 1) * (a - 1) == (b - 1) - (a - 1));
                assert((result - 1) * (a - 1) < b - 1);
            } else {
                assert(result == (b - 1) / (a - 1) + 1);
                // When remainder is non-zero: Verus knows Euclidean division
                assert((b - 1) % (a - 1) != 0);
                assert(0 < (b - 1) % (a - 1) && (b - 1) % (a - 1) < (a - 1));
                assert((result - 1) == (b - 1) / (a - 1));
                assert((result - 1) * (a - 1) == ((b - 1) / (a - 1)) * (a - 1));
                // Since remainder > 0, we have:
                assert(((b - 1) / (a - 1)) * (a - 1) < ((b - 1) / (a - 1)) * (a - 1) + ((b - 1) % (a - 1)));
                assert(((b - 1) / (a - 1)) * (a - 1) < b - 1);
                assert((result - 1) * (a - 1) < b - 1);
            }
            assert(sockets_after_strips(result - 1, a) == 1 + (result - 1) * (a - 1));
            assert(sockets_after_strips(result - 1, a) < b);
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
/* code modified by LLM (iteration 5): No changes needed - implementation is correct */
{
    if b <= 1 {
        proof {
            min_strips_correctness(a as int, b as int, 0);
        }
        return 0;
    }
    
    let numerator: i8 = (b - 1) as i8;
    let denominator: i8 = (a - 1) as i8;
    
    let result = if numerator % denominator == 0 {
        numerator / denominator
    } else {
        numerator / denominator + 1
    };
    
    proof {
        assert(result as int == ceiling_division(numerator as int, denominator as int));
        assert(result as int == ceiling_division((b - 1) as int, (a - 1) as int));
        assert(result as int == min_strips_needed(a as int, b as int));
        min_strips_correctness(a as int, b as int, result as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}