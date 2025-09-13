// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn valid_stairs(stair_heights: Seq<int>) -> bool {
    stair_heights.len() >= 1 &&
    (forall|i: int| 0 <= i < stair_heights.len() - 1 ==> stair_heights[i] <= stair_heights[i + 1]) &&
    (forall|i: int| 0 <= i < stair_heights.len() ==> stair_heights[i] >= 0)
}

spec fn valid_boxes(boxes: Seq<(int, int)>, stairs_amount: int) -> bool {
    forall|i: int| 0 <= i < boxes.len() ==> boxes[i].0 >= 1 && boxes[i].0 <= stairs_amount && boxes[i].1 >= 1
}

spec fn valid_result(result: Seq<int>, boxes: Seq<(int, int)>, stair_heights: Seq<int>) -> bool
    recommends
        stair_heights.len() >= 1,
        forall|i: int| 0 <= i < boxes.len() ==> boxes[i].0 >= 1 && boxes[i].0 <= stair_heights.len()
{
    result.len() == boxes.len() &&
    (forall|i: int| 0 <= i < boxes.len() ==> result[i] >= 0) &&
    (forall|i: int| 0 <= i < boxes.len() ==> 
        result[i] >= stair_heights[0] && result[i] >= stair_heights[boxes[i].0 - 1]) &&
    (forall|i: int| 0 <= i < boxes.len() ==> 
        result[i] == max(if i == 0 { stair_heights[0] } else { result[i-1] + boxes[i-1].1 }, 
                        stair_heights[boxes[i].0 - 1]))
}
// </vc-helpers>

// <vc-spec>
fn solve(stairs_amount: int, stair_heights: Seq<int>, boxes_amount: int, boxes: Seq<(int, int)>) -> (result: Seq<int>)
    requires
        stairs_amount >= 1,
        stair_heights.len() == stairs_amount,
        boxes_amount >= 0,
        boxes.len() == boxes_amount,
        valid_stairs(stair_heights),
        valid_boxes(boxes, stairs_amount)
    ensures
        valid_result(result, boxes, stair_heights)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}