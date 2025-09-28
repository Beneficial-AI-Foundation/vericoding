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
/* helper modified by LLM (iteration 5): removed specs from max_height_up_to_iter and fixed iterative max calculation */

proof fn lemma_max_height_iter_equals_recursive(heights: Seq<int>, idx: int)
    requires
        0 <= idx <= heights.len(),
    ensures
        max_height_up_to_iter(heights, idx) == max_height_up_to(heights, idx - 1),
{
    if idx > 0 {
        if idx - 1 >= 0 {
            lemma_max_height_iter_equals_recursive(heights, idx - 1);
        }
    }
}

spec fn max_height_up_to_iter(heights: Seq<int>, idx: int) -> int {
    if idx <= 0 {
        0
    } else {
        let mut max_so_far = 0;
        let mut i = 0;
        while i < idx
            invariant
                i <= idx,
                0 <= i,
                max_so_far == max_height_up_to(heights, i - 1),
        {
            if heights[i] > max_so_far {
                max_so_far = heights[i];
            }
            i = i + 1;
        }
        max_so_far
    }
}
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
/* code modified by LLM (iteration 5): fixed index handling in max_height_so_far invariant */
{
    let mut count: u32 = 0;
    let mut max_height_so_far: i32 = 0;
    let mut i: usize = 0;

    while i < n as usize
        invariant
            i <= n as usize,
            count as int == count_visible_mountains(heights@.map(|_i: int, x: i32| x as int), i as int),
            max_height_so_far as int == if i == 0 { 0 } else { max_height_up_to(heights@.map(|_i: int, x: i32| x as int), (i - 1) as int) },
    {
        let current_height = heights[i];
        
        if i == 0 || current_height >= max_height_so_far {
            count += 1;
            if current_height > max_height_so_far {
                max_height_so_far = current_height;
            }
        }
        
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}