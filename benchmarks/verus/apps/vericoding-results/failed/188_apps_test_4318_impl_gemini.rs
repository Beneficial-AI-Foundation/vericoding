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
/* helper modified by LLM (iteration 2): reviewed and confirmed correctness */
proof fn lemma_count_visible_mountains_le_n(heights: Seq<int>, n: int)
    requires 0 <= n <= heights.len()
    ensures count_visible_mountains(heights, n) <= n
    decreases n
{
    if n > 0 {
        lemma_count_visible_mountains_le_n(heights, n - 1);
    }
}

/* helper modified by LLM (iteration 2): reviewed and confirmed correctness */
proof fn lemma_count_visible_mountains_non_decreasing(heights: Seq<int>, n1: int, n2: int)
    requires 0 <= n1 <= n2 <= heights.len()
    ensures count_visible_mountains(heights, n1) <= count_visible_mountains(heights, n2)
    decreases n2 - n1
{
    if n1 < n2 {
        lemma_count_visible_mountains_non_decreasing(heights, n1, n2 - 1);
    }
}

/* helper modified by LLM (iteration 3): modified to use a dedicated lemma for the base case */
proof fn lemma_count_visible_mountains_ge_1(heights: Seq<int>, n: int)
    requires
        n > 0,
        n <= heights.len(),
    ensures count_visible_mountains(heights, n) >= 1
{
    lemma_count_visible_mountains_non_decreasing(heights, 1, n);
    lemma_count_visible_mountains_at_1(heights);
}

/* helper modified by LLM (iteration 3): proves the base case for the mountain count */
proof fn lemma_count_visible_mountains_at_1(heights: Seq<int>)
    requires heights.len() >= 1
    ensures count_visible_mountains(heights, 1) == 1
{
    assert(has_ocean_visibility(heights, 0));
}

/* helper modified by LLM (iteration 3): reveals the recursive definition of max_height_up_to */
proof fn lemma_max_height_up_to_recursive(heights: Seq<int>, i: int)
    requires 0 <= i < heights.len()
    ensures max_height_up_to(heights, i) ==
        if i == 0 {
            heights[0]
        } else if heights[i] >= max_height_up_to(heights, i - 1) {
            heights[i]
        } else {
            max_height_up_to(heights, i - 1)
        }
{}

/* helper modified by LLM (iteration 3): reveals the connection between ocean visibility and max height */
proof fn lemma_has_ocean_visibility(heights: Seq<int>, i: int)
    requires 0 <= i < heights.len()
    ensures has_ocean_visibility(heights, i) <==>
        (i == 0 || heights[i] >= max_height_up_to(heights, i - 1))
{}

/* helper modified by LLM (iteration 3): reveals the recursive definition of count_visible_mountains */
proof fn lemma_count_visible_mountains_recursive(heights: Seq<int>, i: int)
    requires 0 <= i < heights.len()
    ensures count_visible_mountains(heights, i + 1) ==
        if has_ocean_visibility(heights, i) {
            count_visible_mountains(heights, i) + 1
        } else {
            count_visible_mountains(heights, i)
        }
{}

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
    /* code modified by LLM (iteration 3): fixed compilation error and used helper lemmas to prove invariants */
    let ghost h_spec = heights@.map(|_i: int, x: i32| x as int);
    let mut count: u32 = 0;
    let mut max_so_far: i32 = 0;
    let mut i: u32 = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == heights.len(),
            h_spec === heights@.map(|_i: int, x: i32| x as int),
            max_so_far as int == max_height_up_to(h_spec, i as int - 1),
            count as int == count_visible_mountains(h_spec, i as int),
        decreases n - i
    {
        let current_height = heights[i as usize];
        
        proof {
            lemma_max_height_up_to_recursive(h_spec, i as int);
            lemma_has_ocean_visibility(h_spec, i as int);
            lemma_count_visible_mountains_recursive(h_spec, i as int);
        }

        if current_height >= max_so_far {
            count = count + 1;
            max_so_far = current_height;
        }
        i = i + 1;
    }

    proof {
        lemma_count_visible_mountains_le_n(h_spec, n as int);
        lemma_count_visible_mountains_ge_1(h_spec, n as int);
    }

    return count;
}

// </vc-code>


}

fn main() {}