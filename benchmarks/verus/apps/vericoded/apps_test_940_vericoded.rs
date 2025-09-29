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
spec fn max_int3(a: int, b: int, c: int) -> int {
    if a >= b && a >= c { a } else if b >= c { b } else { c }
}

/* helper modified by LLM (iteration 3): corrected proof of triangle inequality equivalence */
proof fn lemma_triangle_inequality_form(a: int, b: int, c: int)
    requires
        a > 0, b > 0, c > 0,
    ensures 
        is_triangle(a, b, c) <==> (a + b + c - max_int3(a, b, c) > max_int3(a, b, c)),
{
    let max = max_int3(a, b, c);
    let sum_others = a + b + c - max;

    if a >= b && a >= c {
        assert(max == a);
        assert(sum_others == b + c);
        assert(is_triangle(a, b, c) <==> (b + c > a));
        assert((sum_others > max) <==> (b + c > a));
    } else if b >= c {
        assert(max == b);
        assert(sum_others == a + c);
        assert(is_triangle(a, b, c) <==> (a + c > b));
        assert((sum_others > max) <==> (a + c > b));
    } else {
        assert(max == c);
        assert(sum_others == a + b);
        assert(is_triangle(a, b, c) <==> (a + b > c));
        assert((sum_others > max) <==> (a + b > c));
    }
}

fn max(x: i8, y: i8) -> (res: i8)
    ensures
        res >= x,
        res >= y,
        res == x || res == y,
{
    if x >= y { x } else { y }
}

fn max3(x: i8, y: i8, z: i8) -> (res: i8)
    ensures
        res >= x,
        res >= y,
        res >= z,
        res == x || res == y || res == z,
        res as int == max_int3(x as int, y as int, z as int),
{
    max(x, max(y, z))
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
/* code modified by LLM (iteration 3): fixed compilation errors by using executable types and proof blocks */
{
    proof {
        let a_int = a as int;
        let b_int = b as int;
        let c_int = c as int;
        lemma_triangle_inequality_form(a_int, b_int, c_int);
    }

    let max_val = max3(a, b, c);

    // Using a larger integer type to prevent overflow during sum
    let a_w = a as i16;
    let b_w = b as i16;
    let c_w = c as i16;
    let max_val_w = max_val as i16;
    
    let sum_of_other_two_w = a_w + b_w + c_w - max_val_w;

    if sum_of_other_two_w > max_val_w {
        0i8
    } else {
        let ops = max_val_w - sum_of_other_two_w + 1;
        ops as i8
    }
}
// </vc-code>


}

fn main() {}