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
proof fn lemma_max_height_increases_with_index(heights: Seq<int>, i: int, j: int)
    requires
        heights.len() > 0,
        0 <= i < heights.len(),
        0 <= j < heights.len(),
        i <= j,
    ensures
        max_height_up_to(heights, i) <= max_height_up_to(heights, j),
    decreases j - i
{
    reveal(max_height_up_to);
    if i < j {
        lemma_max_height_increases_with_index(heights, i, j - 1);
        assert(max_height_up_to(heights, j) >= max_height_up_to(heights, j - 1));
    }
}

proof fn lemma_can_make_non_decreasing_prev(heights: Seq<int>, index: int)
    requires
        heights.len() > 0,
        0 <= index < heights.len(),
        heights[index] >= max_height_up_to(heights, index) - 1,
    ensures
        heights[index] >= max_height_up_to(heights, index - 1) - 1,
{
    reveal(max_height_up_to);
    lemma_max_height_increases_with_index(heights, index - 1, index);
}

fn convert_heights_to_int_vec(heights: Vec<i8>) -> Vec<i8>
{
    heights
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: String)
    requires valid_input(n as int, heights@.map(|i: int, v: i8| v as int))
    ensures (result@ == seq!['Y', 'e', 's']) <==> can_make_non_decreasing(heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Add proper function spec and verification */
    let n_usize: usize = n as usize;
    proof {
        assert(valid_input(n as int, heights@.map(|i: int, v: i8| v as int)));
    }
    
    let mut prev_max: i8 = heights[0];
    let mut i: usize = 1;
    
    while i < n_usize
        invariant
            1 <= i <= n_usize,
            prev_max >= 1,
        decreases n_usize - i
    {
        let current = heights[i];
        
        proof {
            assert(heights@[i as int] >= 1);
        }
        
        if current < prev_max - 1 {
            return "No".to_string();
        }
        
        if current > prev_max {
            prev_max = current;
        }
        
        i = i + 1;
    }
    
    "Yes".to_string()
}
// </vc-code>


}

fn main() {}