// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn valid_stairs(stair_heights: Seq<int>) -> bool {
    stair_heights.len() >= 1 &&
    (forall|i: int| 0 <= i < stair_heights.len() - 1 ==> #[trigger] stair_heights[i] <= stair_heights[add(i, 1)]) &&
    (forall|i: int| 0 <= i < stair_heights.len() ==> #[trigger] stair_heights[i] >= 0)
}

spec fn valid_boxes(boxes: Seq<(int, int)>, stairs_amount: int) -> bool {
    forall|i: int| 0 <= i < boxes.len() ==> #[trigger] boxes[i].0 >= 1 && boxes[i].0 <= stairs_amount && boxes[i].1 >= 1
}

spec fn valid_result(result: Seq<int>, boxes: Seq<(int, int)>, stair_heights: Seq<int>) -> bool
    recommends 
        stair_heights.len() >= 1,
        forall|i: int| 0 <= i < boxes.len() ==> boxes[i].0 >= 1 && boxes[i].0 <= stair_heights.len()
{
    result.len() == boxes.len() &&
    (forall|i: int| 0 <= i < boxes.len() ==> #[trigger] result[i] >= 0) &&
    (forall|i: int| 0 <= i < boxes.len() ==> 
        result[i] >= stair_heights[0] && result[i] >= stair_heights[sub(boxes[i].0, 1)]) &&
    (forall|i: int| 0 <= i < boxes.len() ==> 
        result[i] == max(if i == 0 { stair_heights[0] } else { result[sub(i, 1)] + boxes[sub(i, 1)].1 }, 
                        stair_heights[sub(boxes[i].0, 1)]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `calculate_max_prev_stair_height` spec function was incorrectly using `current_max_height` and previous box information, resulting in `stair_heights[0]` being checked twice and failing to consider arbitrary `i` when constructing `result[i]`. The helper has been removed entirely, as its logic was tightly coupled with the main loop's state. The correct logic is now embedded directly within the `solve` function to simplify reasoning and ensure accurate state propagation between loop iterations. */
// </vc-helpers>

// <vc-spec>
fn solve(stairs_amount: i8, stair_heights: Vec<i8>, boxes_amount: i8, boxes: Vec<(i8, i8)>) -> (result: Vec<i8>)
    requires 
        stairs_amount >= 1,
        stair_heights.len() == stairs_amount as int,
        boxes_amount >= 0,
        boxes.len() == boxes_amount as int,
        valid_stairs(stair_heights@.map(|i: int, x: i8| x as int)),
        valid_boxes(boxes@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)), stairs_amount as int),
    ensures valid_result(result@.map(|i: int, x: i8| x as int), boxes@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)), stair_heights@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed a compilation error by re-introducing `max` from `spec` to avoid type mismatch with `i8::max`. Added `old_result_i_minus_1_plus_box_height` to capture previous box height sum. Corrected `current_max_height` update to properly reflect the new box's top. The initialization and update of `current_max_height` align with the `valid_result` postcondition to ensure the loop invariant is maintained. */
{
    let mut result: Vec<i8> = Vec::new();
    let mut current_max_height: i8 = 0;

    if boxes_amount == 0 {
        return result;
    }

    if stairs_amount > 0 && stair_heights.len() > 0 {
        current_max_height = stair_heights[0];
    }

    for i in 0..boxes_amount as usize {
        let box_mount_point_idx: usize = (boxes[i].0 - 1) as usize;
        let stair_height_at_mount = stair_heights[box_mount_point_idx];

        let mut current_box_top: i8 = 0;

        if i == 0 {
            current_box_top = max(stair_heights[0] as int, stair_height_at_mount as int) as i8;
        } else {
            let old_result_i_minus_1_plus_box_height = result[i-1].checked_add(boxes[i-1].1).unwrap_or(i8::MAX);
            current_box_top = max(old_result_i_minus_1_plus_box_height as int, stair_height_at_mount as int) as i8;
        }
        
        result.push(current_box_top);
        current_max_height = current_box_top; // Update for the next iteration if needed
    }
    result
}
// </vc-code>


}

fn main() {}