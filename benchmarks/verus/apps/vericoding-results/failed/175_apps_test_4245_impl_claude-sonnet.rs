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
/* helper modified by LLM (iteration 5): fixed int literal comparison errors */
fn lemma_ceiling_division_correct(x: int, y: int)
    requires y > 0
    ensures
        ceiling_division(x, y) >= 0 || x < 0,
        y * (ceiling_division(x, y) - 1) < x,
        x <= y * ceiling_division(x, y)
{
    if x % y == 0int {
        assert(x == y * (x / y));
    } else if x >= 0int {
        assert(x < y * (x / y + 1));
        assert(x > y * (x / y));
    } else {
        assert(x <= y * (x / y));
        assert(x > y * (x / y - 1));
    }
}

fn lemma_min_strips_correct(a: int, b: int)
    requires valid_input(a, b)
    ensures correct_result(a, b, min_strips_needed(a, b))
{
    let strips = min_strips_needed(a, b);
    if b <= 1int {
        assert(strips == 0);
        assert(sockets_after_strips(0, a) == 1);
        assert(sockets_after_strips(0, a) >= b);
    } else {
        lemma_ceiling_division_correct(b - 1int, a - 1int);
        let cd = ceiling_division(b - 1int, a - 1int);
        assert(strips == cd);
        assert((a - 1) * (cd - 1) < b - 1);
        assert(b - 1 <= (a - 1) * cd);
        
        if cd > 0int {
            assert(sockets_after_strips(cd - 1, a) == 1 + (cd - 1) * (a - 1));
            assert(1 + (cd - 1) * (a - 1) < b);
        }
        
        assert(sockets_after_strips(cd, a) == 1 + cd * (a - 1));
        assert(1 + cd * (a - 1) >= b);
    }
}

fn lemma_sockets_monotonic(strips1: int, strips2: int, a: int)
    requires a > 1, strips1 <= strips2, strips1 >= 0, strips2 >= 0
    ensures sockets_after_strips(strips1, a) <= sockets_after_strips(strips2, a)
{
    assert(sockets_after_strips(strips2, a) - sockets_after_strips(strips1, a) == (strips2 - strips1) * (a - 1));
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures correct_result(a as int, b as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int literal comparison errors */
    if b <= 1i8 {
        return 0i8;
    }
    
    let numerator = b - 1i8;
    let denominator = a - 1i8;
    
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    
    let result = if remainder == 0i8 {
        quotient
    } else {
        quotient + 1i8
    };
    
    proof {
        lemma_min_strips_correct(a as int, b as int);
        assert(result as int == min_strips_needed(a as int, b as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}