// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, y: int, z: int) -> bool {
    x >= 1 && y >= 1 && z >= 1 && y + 2 * z <= x
}

spec fn max_people(x: int, y: int, z: int) -> int
    recommends valid_input(x, y, z)
{
    (x - z) / (y + z)
}

spec fn valid_solution(x: int, y: int, z: int, result: int) -> bool
    recommends valid_input(x, y, z)
{
    result == max_people(x, y, z) &&
    result >= 0 &&
    result * (y + z) <= x - z < (result + 1) * (y + z)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use assert_by_compute for division properties */
proof fn div_properties(num: int, den: int, r: int)
    requires
        den > 0,
        r == num / den,
    ensures
        r * den <= num,
        num < (r + 1) * den,
{
    // Use Verus's built-in division properties
    assert(r * den <= num) by(nonlinear_arith)
        requires den > 0, r == num / den;
    assert(num < (r + 1) * den) by(nonlinear_arith)
        requires den > 0, r == num / den;
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8, z: i8) -> (result: i8)
    requires valid_input(x as int, y as int, z as int)
    ensures valid_solution(x as int, y as int, z as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified proof structure */
    let numerator: i8 = x - z;
    let denominator: i8 = y + z;
    let result: i8 = numerator / denominator;
    
    proof {
        assert(numerator as int == (x as int) - (z as int));
        assert(denominator as int == (y as int) + (z as int));
        assert(denominator >= 2) by {
            assert(y >= 1);
            assert(z >= 1);
        }
        assert(numerator >= 0) by {
            assert((y as int) + 2 * (z as int) <= (x as int));
            assert((x as int) - (z as int) >= (y as int) + (z as int));
            assert((y as int) + (z as int) >= 2);
        }
        
        let num = numerator as int;
        let den = denominator as int;
        let r = result as int;
        
        assert(r == num / den);
        assert(num == (x as int) - (z as int));
        assert(den == (y as int) + (z as int));
        assert(den > 0);
        
        // Call the helper to establish division properties
        div_properties(num, den, r);
        
        assert(r == max_people(x as int, y as int, z as int));
        assert(r * ((y as int) + (z as int)) <= (x as int) - (z as int));
        assert((x as int) - (z as int) < (r + 1) * ((y as int) + (z as int)));
        assert(result as int >= 0) by {
            assert(num >= 0);
            assert(den > 0);
            assert(r == num / den);
        }
        assert(valid_solution(x as int, y as int, z as int, result as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}