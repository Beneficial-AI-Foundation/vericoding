// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool {
  a >= 1 && b > a && b < 499500
}

spec fn valid_snow_depth(a: int, b: int, depth: int) -> bool {
  depth >= 1 &&
  ((b - a) * (b - a) - (a + b)) >= 2 &&
  ((b - a) * (b - a) - (a + b)) % 2 == 0
}

spec fn snow_depth_formula(a: int, b: int) -> int
  recommends valid_input(a, b) && valid_snow_depth(a, b, ((b - a) * (b - a) - (a + b)) / 2)
{
  ((b - a) * (b - a) - (a + b)) / 2
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
  requires valid_input(a as int, b as int) && valid_snow_depth(a as int, b as int, ((b as int - a as int) * (b as int - a as int) - (a as int + b as int)) / 2)
  ensures result as int >= 1 && result as int == snow_depth_formula(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix compilation error by computing in i8 and using proof block for int operations */
    let diff = b - a;
    let diff_squared = diff * diff;
    let sum = a + b;
    let depth_times_2_i8 = diff_squared - sum;
    
    proof {
        let depth_times_2 = (diff as int * diff as int) - (a as int + b as int);
        assert(depth_times_2 == depth_times_2_i8 as int);
        assert(depth_times_2 >= 2);
        assert(depth_times_2 % 2 == 0);
    }
    
    let result = depth_times_2_i8 / 2;
    
    proof {
        assert(result as int == snow_depth_formula(a as int, b as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}