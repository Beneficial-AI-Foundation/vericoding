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
proof fn lemma_max_height_properties(heights: Seq<int>, index: int)
    requires
        heights.len() > 0,
        0 <= index < heights.len(),
        forall|i: int| 0 <= i < heights.len() ==> heights[i] >= 1,
    ensures
        max_height_up_to(heights, index) >= 1,
        max_height_up_to(heights, index) <= index + 1,
        forall|j: int| 0 <= j <= index ==> heights[j] <= max_height_up_to(heights, index),
    decreases index + 1
{
    if index == 0 {
        assert(max_height_up_to(heights, 0) == heights[0]);
        assert(heights[0] >= 1);
    } else {
        lemma_max_height_properties(heights, index - 1);
        if heights[index] > max_height_up_to(heights, index - 1) {
            assert(max_height_up_to(heights, index) == heights[index]);
            assert(heights[index] >= 1);
            assert(heights[index] <= index + 1);
        } else {
            assert(max_height_up_to(heights, index) == max_height_up_to(heights, index - 1));
            assert(max_height_up_to(heights, index - 1) <= index);
        }
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
    /* code modified by LLM (iteration 5): add decreases clause to while loop */
    let ghost heights_int = heights@.map(|i: int, v: i8| v as int);
    let mut i: usize = 0;
    let mut max_so_far: i8 = 0;
    let mut can_fix = true;
    
    while i < n as usize
        invariant
            0 <= i <= n as int,
            n as int == heights.len(),
            heights_int == heights@.map(|j: int, v: i8| v as int),
            valid_input(n as int, heights_int),
            max_so_far as int == if i == 0 { 0 } else { max_height_up_to(heights_int, (i - 1) as int) },
            can_fix <==> (forall|j: int| 0 <= j < i as int ==> heights_int[j] >= max_height_up_to(heights_int, j) - 1),
        decreases n as usize - i
    {
        let current = heights[i];
        
        if i == 0 {
            max_so_far = current;
        } else {
            if current < max_so_far - 1 {
                can_fix = false;
            }
            if current > max_so_far {
                max_so_far = current;
            }
        }
        
        proof {
            if i > 0 {
                lemma_max_height_properties(heights_int, (i - 1) as int);
            }
            assert(max_so_far as int == max_height_up_to(heights_int, i as int));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == n as usize);
        assert(can_fix <==> (forall|j: int| 0 <= j < heights_int.len() ==> heights_int[j] >= max_height_up_to(heights_int, j) - 1));
        assert(can_fix <==> can_make_non_decreasing(heights_int));
    }
    
    if can_fix {
        let result = "Yes".to_string();
        proof {
            assert(result@ == seq!['Y', 'e', 's']);
        }
        result
    } else {
        let result = "No".to_string();
        proof {
            assert(result@ == seq!['N', 'o']);
            assert(result@ != seq!['Y', 'e', 's']);
        }
        result
    }
}
// </vc-code>


}

fn main() {}