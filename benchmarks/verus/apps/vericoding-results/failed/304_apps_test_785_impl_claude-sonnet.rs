// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int) -> bool {
    n > 0 && a > 0 && b > 0
}

spec fn valid_output(result: Seq<int>, n: int, a: int, b: int) -> bool {
    result.len() == 3 &&
    result[0] >= 6 * n &&
    result[1] > 0 && result[2] > 0 &&
    result[0] == result[1] * result[2] &&
    ((result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove invalid cast and use computational approach */
spec fn safe_mult_i8(x: int, y: int) -> bool {
    let result = x * y;
    result >= i8::MIN && result <= i8::MAX
}

spec fn min_area_for_dimensions(a: int, b: int, n: int) -> int {
    let min_dim = if a <= b { a } else { b };
    let max_dim = if a <= b { b } else { a };
    let min_area = 6 * n;
    let needed_area = ((min_area + min_dim - 1) / min_dim) * min_dim;
    if needed_area >= min_area && needed_area / min_dim >= max_dim {
        needed_area
    } else {
        ((min_area + max_dim - 1) / max_dim) * max_dim
    }
}

fn compute_i8_from_int(x: int) -> (result: i8)
    requires x >= i8::MIN && x <= i8::MAX
    ensures result as int == x
{
    if x >= 0 {
        if x <= 127 {
            x as u8 as i8
        } else {
            127i8
        }
    } else {
        if x >= -128 {
            -((-x) as u8) as i8
        } else {
            -128i8
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, a as int, b as int)
    ensures valid_output(result@.map(|i, x| x as int), n as int, a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use computational conversion instead of direct cast */
    let ghost min_area = 6 * (n as int);
    let min_dim = if a <= b { a } else { b };
    let max_dim = if a <= b { b } else { a };
    
    // Calculate area that satisfies both >= 6*n and is divisible by dimensions
    let ghost area_option1 = ((min_area + (min_dim as int) - 1) / (min_dim as int)) * (min_dim as int);
    let ghost area_option2 = ((min_area + (max_dim as int) - 1) / (max_dim as int)) * (max_dim as int);
    
    let ghost area = if area_option1 >= min_area && (area_option1 / (min_dim as int)) >= (max_dim as int) {
        area_option1
    } else {
        area_option2
    };
    
    let ghost w1 = area / (min_dim as int);
    let ghost w2 = min_dim as int;
    
    let area_i8 = compute_i8_from_int(area);
    let w1_i8 = compute_i8_from_int(w1);
    let w2_i8 = compute_i8_from_int(w2);
    
    let result = vec![area_i8, w1_i8, w2_i8];
    
    proof {
        assert(result@.len() == 3);
        assert(result@[0] == area_i8);
        assert(result@[1] == w1_i8);
        assert(result@[2] == w2_i8);
        assert(area >= 6 * (n as int));
        assert(w1 > 0 && w2 > 0);
        assert(area == w1 * w2);
        assert((w1 >= a as int && w2 >= b as int) || (w1 >= b as int && w2 >= a as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}