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
/* helper modified by LLM (iteration 4): identity lemma for snow_depth_formula definition */
proof fn snow_depth_identity(a: int, b: int)
    requires
        valid_input(a, b),
        valid_snow_depth(a, b, ((b - a) * (b - a) - (a + b)) / 2),
    ensures
        snow_depth_formula(a, b) == ((b - a) * (b - a) - (a + b)) / 2,
{
    assert(snow_depth_formula(a, b) == ((b - a) * (b - a) - (a + b)) / 2);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
  requires valid_input(a as int, b as int) && valid_snow_depth(a as int, b as int, ((b as int - a as int) * (b as int - a as int) - (a as int + b as int)) / 2)
  ensures result as int >= 1 && result as int == snow_depth_formula(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute using i32 in exec context; relate to spec in proof block */
    let ai32: i32 = a as i32;
    let bi32: i32 = b as i32;
    let diff: i32 = bi32 - ai32;
    let num: i32 = diff * diff - (ai32 + bi32);
    let depth32: i32 = num / 2;
    proof {
        let ai: int = a as int;
        let bi: int = b as int;
        assert(snow_depth_formula(ai, bi) == ((bi - ai) * (bi - ai) - (ai + bi)) / 2);
    }
    depth32 as i8
}
// </vc-code>


}

fn main() {}