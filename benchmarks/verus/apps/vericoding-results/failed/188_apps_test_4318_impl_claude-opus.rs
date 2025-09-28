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
proof fn lemma_max_height_properties(heights: Seq<int>, idx: int)
    requires
        0 <= idx < heights.len(),
    ensures
        max_height_up_to(heights, idx) >= heights[0],
        idx > 0 ==> max_height_up_to(heights, idx) >= max_height_up_to(heights, idx - 1),
        forall|i: int| 0 <= i <= idx ==> heights[i] <= max_height_up_to(heights, idx),
    decreases idx
{
    if idx == 0 {
    } else {
        lemma_max_height_properties(heights, idx - 1);
        if heights[idx] >= max_height_up_to(heights, idx - 1) {
            assert(max_height_up_to(heights, idx) == heights[idx]);
        } else {
            assert(max_height_up_to(heights, idx) == max_height_up_to(heights, idx - 1));
        }
    }
}

proof fn lemma_has_visibility_max_height(heights: Seq<int>, idx: int)
    requires
        0 <= idx < heights.len(),
        has_ocean_visibility(heights, idx),
    ensures
        heights[idx] == max_height_up_to(heights, idx),
{
    if idx == 0 {
    } else {
        assert(heights[idx] >= max_height_up_to(heights, idx - 1));
        if heights[idx] > max_height_up_to(heights, idx - 1) {
            assert(max_height_up_to(heights, idx) == heights[idx]);
        } else {
            assert(max_height_up_to(heights, idx) == heights[idx]);
        }
    }
}

proof fn lemma_count_visible_bounds(heights: Seq<int>, n: int)
    requires
        0 <= n <= heights.len(),
    ensures
        0 <= count_visible_mountains(heights, n) <= n,
    decreases n
{
    if n <= 0 {
    } else {
        lemma_count_visible_bounds(heights, n - 1);
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
{
    /* code modified by LLM (iteration 3): added decreases clause to while loop */
    let ghost heights_spec = heights@.map(|_i: int, x: i32| x as int);
    let mut count: u32 = 0;
    let mut max_so_far: i32 = 0;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            count <= i,
            1 <= count + (n - i) <= n,
            count as int == count_visible_mountains(heights_spec, i as int),
            i > 0 ==> max_so_far as int == max_height_up_to(heights_spec, (i - 1) as int),
            i == 0 ==> max_so_far == 0,
        decreases n - i
    {
        proof {
            lemma_count_visible_bounds(heights_spec, i as int);
            lemma_count_visible_bounds(heights_spec, (i + 1) as int);
        }
        
        let current_height = heights[i as usize];
        
        if i == 0 || current_height >= max_so_far {
            count = count + 1;
            max_so_far = current_height;
            
            proof {
                assert(has_ocean_visibility(heights_spec, i as int));
                assert(count_visible_mountains(heights_spec, (i + 1) as int) == 1 + count_visible_mountains(heights_spec, i as int));
                if i > 0 {
                    lemma_has_visibility_max_height(heights_spec, i as int);
                    assert(max_so_far as int == heights_spec[i as int]);
                    assert(max_so_far as int == max_height_up_to(heights_spec, i as int));
                }
            }
        } else {
            proof {
                assert(!has_ocean_visibility(heights_spec, i as int));
                assert(count_visible_mountains(heights_spec, (i + 1) as int) == count_visible_mountains(heights_spec, i as int));
                if max_so_far as int > current_height as int {
                    lemma_max_height_properties(heights_spec, (i - 1) as int);
                    assert(max_height_up_to(heights_spec, i as int) == max_so_far as int);
                }
            }
        }
        
        if current_height > max_so_far {
            max_so_far = current_height;
        }
        
        proof {
            if i > 0 {
                lemma_max_height_properties(heights_spec, i as int);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_count_visible_bounds(heights_spec, n as int);
    }
    
    count
}
// </vc-code>


}

fn main() {}