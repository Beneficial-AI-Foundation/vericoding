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
{
    /* code modified by LLM (iteration 2): fixed compilation error by using i64 in executable code */
    let mut max_so_far: i64 = 0;
    let mut i: usize = 0;
    while i < heights.len()
        invariant
            0 <= i <= heights.len()
        decreases heights.len() - i
    {
        let h: i64 = heights[i] as i64;
        if h < max_so_far - 1 {
            return "No".to_string();
        } else if h > max_so_far {
            max_so_far = h;
        }
        i += 1;
    }
    return "Yes".to_string();
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: String)
    requires valid_input(n as int, heights@.map(|i: int, v: i8| v as int))
    ensures (result@ == seq!['Y', 'e', 's']) <==> can_make_non_decreasing(heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>

// </vc-code>


}

fn main() {}