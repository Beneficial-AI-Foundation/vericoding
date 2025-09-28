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
/* helper modified by LLM (iteration 5): induction lemma ensuring loop step preserves spec counts */
proof fn lemma_step(heights: Seq<int>, i: int, count: int, max_v: int)
    requires
        0 <= i,
        i < heights.len(),
        count == count_visible_mountains(heights, i),
        max_v == max_height_up_to(heights, i - 1),
    ensures
        count_visible_mountains(heights, i + 1) == if heights[i] >= max_v { count + 1 } else { count },
        max_height_up_to(heights, i) == if heights[i] >= max_v { heights[i] } else { max_v },
    decreases
        heights.len() - i,
{
    if heights[i] >= max_v {
        // visible at i
        assert(has_ocean_visibility(heights, i));
        assert(count_visible_mountains(heights, i + 1) == 1 + count_visible_mountains(heights, i));
        assert(count_visible_mountains(heights, i + 1) == if heights[i] >= max_v { count + 1 } else { count });
        assert(max_height_up_to(heights, i) == heights[i]);
    } else {
        // not visible at i
        // by definition of has_ocean_visibility and max_height_up_to
        assert(!(heights[i] >= max_v));
        assert(count_visible_mountains(heights, i + 1) == count_visible_mountains(heights, i));
        assert(count_visible_mountains(heights, i + 1) == if heights[i] >= max_v { count + 1 } else { count });
        assert(max_height_up_to(heights, i) == max_v);
    }
}

/* helper modified by LLM (iteration 5): there is at least one visible mountain when n > 0 */
proof fn lemma_count_at_least_one(heights: Seq<int>, n: int)
    requires
        0 < n,
        n <= heights.len(),
    ensures
        count_visible_mountains(heights, n) >= 1,
    decreases
        n,
{
    if n == 1 {
        // index 0 always has ocean visibility
        assert(has_ocean_visibility(heights, 0));
        assert(count_visible_mountains(heights, 1) == 1);
    } else {
        lemma_count_at_least_one(heights, n - 1);
        if has_ocean_visibility(heights, n - 1) {
            assert(count_visible_mountains(heights, n) == 1 + count_visible_mountains(heights, n - 1));
            assert(count_visible_mountains(heights, n) >= 1);
        } else {
            assert(count_visible_mountains(heights, n) == count_visible_mountains(heights, n - 1));
            assert(count_visible_mountains(heights, n) >= 1);
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
/* code modified by LLM (iteration 5): compute visible mountains iteratively */
{
    let mut i: usize = 0usize;
    let mut count: usize = 0usize;
    let mut max_v: i32 = 0;
    let seq = heights@.map(|_j: int, x: i32| x as int);
    while i < n as usize
        invariant
            0 <= i as int <= n as int,
            count as int == count_visible_mountains(seq, i as int),
            max_v as int == max_height_up_to(seq, i as int - 1),
        decreases (n as int) - (i as int)
    {
        // ensure indexing preconditions for the Vec access
        proof {
            assert(i as int < n as int);
            assert(i < heights.len());
        }
        let h = heights[i];
        // use lemma to relate current state to next state
        proof {
            lemma_step(seq, i as int, count as int, max_v as int);
        }
        if h >= max_v {
            count = count + 1;
            max_v = h;
        }
        i = i + 1;
    }
    let result = count as u32;
    proof {
        lemma_count_at_least_one(seq, n as int);
        assert(result as int == count_visible_mountains(seq, n as int));
    }
    result
}

// </vc-code>


}

fn main() {}