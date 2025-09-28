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
spec fn can_make_non_decreasing_recursive(heights: Seq<int>, index: int) -> bool
    decreases index
{
    if index == 0 {
        true
    } else {
        let prev_max = max_height_up_to(heights, index - 1);
        heights[index] >= prev_max - 1 && can_make_non_decreasing_recursive(heights, index - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: String)
    requires valid_input(n as int, heights@.map(|i: int, v: i8| v as int))
    ensures (result@ == seq!['Y', 'e', 's']) <==> can_make_non_decreasing(heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    let heights_spec = heights@.map(|_i: int, v: i8| v as int);

    if heights_spec.len() == 0 {
        return "Yes".to_string();
    }

    let mut current_max_seen: i8 = 0;
    let mut i: int = 0;

    while i < n as int
        invariant
            0 <= i <= n as int,
            current_max_seen as int == max_height_up_to(heights_spec, i - 1),
            forall|j: int| 0 <= j < i ==> heights_spec[j] >= max_height_up_to(heights_spec, j) - 1
    {
        let height = heights_spec[i];
        if height < current_max_seen - 1 {
            return "No".to_string();
        }
        if height > current_max_seen {
            current_max_seen = height;
        }
        i = i + 1;
    }

    "Yes".to_string()
}
// </vc-code>


}

fn main() {}