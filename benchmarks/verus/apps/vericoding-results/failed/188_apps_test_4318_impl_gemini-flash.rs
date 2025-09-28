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
/* code modified by LLM (iteration 4): Added decreases clause to the while loop and fixed invariant related to `max_h_so_far` */
{
    let mut visible_mountains: u32 = 0;
    let mut max_h_so_far: i32 = 0;

    let mut i: u32 = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            0 <= visible_mountains,
            visible_mountains <= i,
            max_h_so_far as int == (if i == 0 { 0 } else { max_height_up_to(heights@.map(|_i: int, x: i32| x as int), i as int - 1) }),
            visible_mountains as int == count_visible_mountains(heights@.map(|_i: int, x: i32| x as int), i as int),
        decreases (n - i)
    {
        if heights[i as usize] >= max_h_so_far {
            visible_mountains = visible_mountains + 1;
        }
        max_h_so_far = if heights[i as usize] > max_h_so_far { heights[i as usize] } else { max_h_so_far };
        i = i + 1;
    }
    visible_mountains
}
// </vc-code>


}

fn main() {}