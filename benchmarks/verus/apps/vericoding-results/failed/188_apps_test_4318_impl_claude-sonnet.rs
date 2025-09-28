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
/* helper modified by LLM (iteration 5): fixed bounds and added better proof structure */
proof fn lemma_max_height_up_to_monotonic(heights: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j < heights.len(),
    ensures
        max_height_up_to(heights, i) <= max_height_up_to(heights, j),
    decreases j - i
{
    if i == j {
        // trivial
    } else {
        lemma_max_height_up_to_monotonic(heights, i, j - 1);
    }
}

proof fn lemma_count_visible_mountains_bounds(heights: Seq<int>, n: int)
    requires
        n >= 0,
        heights.len() >= n,
    ensures
        0 <= count_visible_mountains(heights, n) <= n,
    decreases n
{
    if n <= 0 {
        // trivial
    } else {
        lemma_count_visible_mountains_bounds(heights, n - 1);
    }
}

proof fn lemma_count_visible_mountains_at_least_one(heights: Seq<int>, n: int)
    requires
        n > 0,
        heights.len() >= n,
    ensures
        count_visible_mountains(heights, n) >= 1,
    decreases n
{
    if n == 1 {
        // The first mountain is always visible
    } else {
        if has_ocean_visibility(heights, n - 1) {
            lemma_count_visible_mountains_bounds(heights, n - 1);
        } else {
            lemma_count_visible_mountains_at_least_one(heights, n - 1);
        }
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
/* code modified by LLM (iteration 5): fixed indexing bounds and improved invariants */
{
    let mut count: u32 = 0;
    let mut max_height: i32 = 0;
    let mut i: u32 = 0;
    let ghost spec_heights = heights@.map(|_i: int, x: i32| x as int);
    
    proof {
        lemma_count_visible_mountains_at_least_one(spec_heights, n as int);
    }
    
    while i < n
        invariant
            i <= n,
            0 <= count <= i,
            count as int == count_visible_mountains(spec_heights, i as int),
            i > 0 ==> (i - 1 < heights.len() && max_height == max_height_up_to(spec_heights, (i - 1) as int)),
        decreases n - i
    {
        if i == 0 {
            count = count + 1;
            max_height = heights[0];
        } else {
            if heights[i as usize] >= max_height {
                count = count + 1;
                max_height = heights[i as usize];
            }
        }
        
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}