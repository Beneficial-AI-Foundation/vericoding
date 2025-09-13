// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_height_up_to(heights: Seq<int>, up_to_index: int) -> int
  recommends 0 <= up_to_index < heights.len()
  decreases up_to_index
{
  if up_to_index == 0 { heights[up_to_index] }
  else if heights[up_to_index] >= max_height_up_to(heights, up_to_index - 1) { heights[up_to_index] }
  else { max_height_up_to(heights, up_to_index - 1) }
}

spec fn has_ocean_visibility(heights: Seq<int>, mountain_index: int) -> bool
  recommends 0 <= mountain_index < heights.len()
{
  mountain_index == 0 || heights[mountain_index] >= max_height_up_to(heights, mountain_index - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, heights: Seq<int>) -> (result: int)
  requires 
    n > 0,
    heights.len() == n,
    n <= 20,
    forall|i: int| 0 <= i < n ==> 1 <= heights[i] <= 100
  ensures 
    1 <= result <= n,
    result == Set::new(|i: int| 0 <= i < n && has_ocean_visibility(heights, i)).len()
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}