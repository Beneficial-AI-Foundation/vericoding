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
proof fn lemma_check_equiv(h: int, m: int)
    ensures
        (h >= m - 1) <==> (h >= (if h > m {h} else {m}) - 1),
{}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: String)
    requires valid_input(n as int, heights@.map(|i: int, v: i8| v as int))
    ensures (result@ == seq!['Y', 'e', 's']) <==> can_make_non_decreasing(heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    let hs = heights@.map(|_i: int, v: i8| v as int);
    let mut max_h: int = 0;
    let mut i: usize = 0;
    while i < n as usize
        invariant
            n as int == hs.len(),
            heights@.map(|_i: int, v: i8| v as int) == hs,
            valid_input(n as int, hs),
            0 <= i <= n as usize,
            max_h == max_height_up_to(hs, i as int - 1),
            forall|j: int| 0 <= j < i as int ==> hs[j] >= max_height_up_to(hs, j) - 1,
        decreases n as usize - i
    {
        let h = heights[i] as int;
        lemma_check_equiv(h, max_h);

        if h < max_h - 1 {
            assert(!can_make_non_decreasing(hs));
            return "No".to_string();
        }

        if h > max_h {
            max_h = h;
        }

        i = i + 1;
    }

    assert(can_make_non_decreasing(hs));
    return "Yes".to_string();
}
// </vc-code>


}

fn main() {}