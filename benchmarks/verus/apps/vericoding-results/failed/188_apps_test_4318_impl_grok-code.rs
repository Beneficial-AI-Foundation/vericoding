// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_height_up_to(heights: Seq<int>, up_to_index: int) -> int
    decreases up_to_index
{
    if 0 <= up_to_index < heights.len() {
        if up_to_index == 0 {
            heights[0]
        } else if heights[up_to_index] >= max_height_up_to(heights, up_to_index - 1) {
            heights[up_to_index]
        } else {
            max_height_up_to(heights, up_to_index - 1)
        }
    } else {
        0
    }
}

spec fn has_ocean_visibility(heights: Seq<int>, mountain_index: int) -> bool {
    if 0 <= mountain_index < heights.len() {
        mountain_index == 0 || heights[mountain_index] >= max_height_up_to(heights, mountain_index - 1)
    } else {
        false
    }
}

spec fn count_visible_mountains(heights: Seq<int>, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else if has_ocean_visibility(heights, n - 1) {
        1 + count_visible_mountains(heights, n - 1)
    } else {
        count_visible_mountains(heights, n - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): empty as no helpers needed */

// </vc-helpers>

// <vc-spec>
fn solve(n: u32, heights: Vec<i32>) -> (result: u32)
    requires 
        n > 0,
        heights.len() == n,
        n <= 20,
        forall|i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] as int <= 100,
    ensures 
        1 <= result <= n,
        result as int == count_visible_mountains(heights@.map(|_i: int, x: i32| x as int), n as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): defined heights_seq to avoid repeated map and fixed lambda variable naming to prevent shadowing issues */
{
    let heights_seq = heights@.map(|index: int, x: i32| x as int);
    let mut count: u32 = 0;
    let mut max_h: i32 = 0;
    let mut i = 0;
    while i < n as usize
        invariant
            0 <= i <= n as usize,
            count as int == count_visible_mountains(heights_seq, i as int),
            max_h as int == max_height_up_to(heights_seq, (i as int) - 1),
            0 <= count as int <= n as int,
        decreases n as usize - i
    {
        let h = heights[i];
        if h >= max_h {
            count += 1;
        }
        max_h = if h > max_h { h } else { max_h };
        i += 1;
    }
    count
}
// </vc-code>


}

fn main() {}