// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_height_up_to(heights: Seq<int>, index: int) -> int
    decreases index + 1
{
    if heights.len() > 0 && -1 <= index < heights.len() {
        if index < 0 {
            0
        } else if index == 0 {
            heights[0]
        } else if heights[index] > max_height_up_to(heights, index - 1) {
            heights[index]
        } else {
            max_height_up_to(heights, index - 1)
        }
    } else {
        0
    }
}

spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n >= 1 && heights.len() == n && (forall|i: int| 0 <= i < heights.len() ==> heights[i] >= 1)
}

spec fn can_make_non_decreasing(heights: Seq<int>) -> bool {
    if heights.len() > 0 {
        forall|i: int| 0 <= i < heights.len() ==> heights[i] >= max_height_up_to(heights, i) - 1
    } else {
        true
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed Seq indexing syntax using @ operator */
proof fn lemma_max_height_monotonic(heights: Seq<int>, i: int, j: int)
    requires
        heights.len() > 0,
        0 <= i <= j < heights.len(),
    ensures max_height_up_to(heights, i) <= max_height_up_to(heights, j)
    decreases j - i
{
    if i == j {
        // Base case: trivially true
    } else {
        lemma_max_height_monotonic(heights, i, j - 1);
        // max_height_up_to(heights, j) is either heights[j] or max_height_up_to(heights, j-1)
        // In both cases, it's >= max_height_up_to(heights, j-1) >= max_height_up_to(heights, i)
    }
}

proof fn lemma_max_height_bounds(heights: Seq<int>, i: int)
    requires
        heights.len() > 0,
        0 <= i < heights.len(),
    ensures max_height_up_to(heights, i) >= heights[i]
    decreases i + 1
{
    if i == 0 {
        // Base case: max_height_up_to(heights, 0) == heights[0]
    } else {
        lemma_max_height_bounds(heights, i - 1);
        // max_height_up_to(heights, i) is max of heights[i] and max_height_up_to(heights, i-1)
    }
}

fn compute_max_height_up_to(heights_int: Seq<int>, index: usize) -> (result: i8)
    requires
        heights_int.len() > 0,
        index < heights_int.len(),
        forall|j: int| 0 <= j < heights_int.len() ==> 1 <= heights_int[j] <= 127,
    ensures result as int == max_height_up_to(heights_int, index as int)
{
    let mut max_height = heights_int@[0];
    let mut i = 1;
    while i <= index
        invariant
            1 <= i <= index + 1,
            max_height == max_height_up_to(heights_int, (i - 1) as int),
            1 <= max_height <= 127,
    {
        if heights_int@[i] > max_height {
            max_height = heights_int@[i];
        }
        i += 1;
    }
    max_height as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: String)
    requires valid_input(n as int, heights@.map(|i: int, v: i8| v as int))
    ensures (result@ == seq!['Y', 'e', 's']) <==> can_make_non_decreasing(heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed Seq indexing and simplified implementation */
    let ghost heights_int = heights@.map(|i: int, v: i8| v as int);
    
    let mut i = 0usize;
    while i < heights.len()
        invariant
            0 <= i <= heights.len(),
            heights_int == heights@.map(|i: int, v: i8| v as int),
            forall|j: int| 0 <= j < i ==> heights_int@[j] >= max_height_up_to(heights_int, j) - 1,
    {
        let current_height_exec = heights[i];
        
        // Simple heuristic check in exec code
        if i > 0 {
            let max_so_far_exec = compute_max_height_up_to(heights_int, i);
            if current_height_exec < max_so_far_exec - 1 {
                return "No".to_string();
            }
        }
        
        i += 1;
    }
    
    "Yes".to_string()
}
// </vc-code>


}

fn main() {}