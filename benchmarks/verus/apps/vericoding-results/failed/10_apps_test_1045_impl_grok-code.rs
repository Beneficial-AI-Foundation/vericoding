// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn cubes_for_level(level: int) -> int
    recommends level >= 1
{
    level * (level + 1) / 2
}

spec fn total_cubes_for_height(h: int) -> int
    recommends h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

spec fn valid_pyramid_height(n: int, h: int) -> bool {
    valid_input(n) && h >= 1 && 
    total_cubes_for_height(h) <= n &&
    total_cubes_for_height(h + 1) > n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result >= 1 &&
        valid_pyramid_height(n as int, result as int)
// </vc-spec>
// <vc-code>
   /* code modified by LLM (iteration 3): fixed compilation by using i8 for all exec variables and computations */
   {
       let mut h: i8 = 0;
       let mut prev_total: i8 = 0;
       while true
           invariant
               (prev_total as int) == total_cubes_for_height(h as int),
               (h as int) >= 0,
           decreases n as int - prev_total as int
       {
           let current_cubes: i8 = ((h + 1) * (h + 2)) / 2;
           let next_total: i8 = prev_total + current_cubes;
           if next_total > n {
               break;
           }
           prev_total = next_total;
           h = h + 1;
       }
       h
   }
// </vc-code>


}

fn main() {}