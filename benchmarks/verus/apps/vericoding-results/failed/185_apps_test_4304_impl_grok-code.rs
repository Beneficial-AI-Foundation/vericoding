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
/* helper modified by LLM (iteration 5): used i32 for exec calculcations to avoid 'int' in exec code, used proof assertions for verification */
fn compute_snow_depth(a: i8, b: i8) -> (res: i8)
    requires
        (b as int - a as int) >= 0,
        (a as int + b as int) >= 0
    ensures
        (res as int) == snow_depth_formula(a as int, b as int)
    decreases (b as int - a as int)
{
    let diff: i32 = b as i32 - a as i32;
    let sum_ab: i32 = a as i32 + b as i32;
    let sq: i32 = diff * diff;
    let numer: i32 = sq - sum_ab;
    proof {
        let expected = snow_depth_formula(a as int, b as int);
        assert(expected == (numer as int) / 2);
        assert(expected >= 1 && expected <= 127);
        assert(valid_input(a as int, b as int));
        assert(valid_snow_depth(a as int, b as int, expected));
        assert(numer % 2 == 0);
    }
    (numer / 2) as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
  requires valid_input(a as int, b as int) && valid_snow_depth(a as int, b as int, ((b as int - a as int) * (b as int - a as int) - (a as int + b as int)) / 2)
  ensures result as int >= 1 && result as int == snow_depth_formula(a as int, b as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): call helper function */
{
    compute_snow_depth(a, b)
}
// </vc-code>


}

fn main() {}