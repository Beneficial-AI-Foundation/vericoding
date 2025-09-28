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
{
    /* code modified by LLM (iteration 3): Added decreases clause to fix loop verification */
    let mut result: Vec<i8> = Vec::new();
    let mut current_height: i8 = 0;
    let mut i: usize = 0;
    
    while i < boxes.len()
        invariant
            i <= boxes.len(),
            result.len() == i,
            boxes.len() == boxes_amount as int,
            stair_heights.len() == stairs_amount as int,
            stairs_amount >= 1,
            valid_stairs(stair_heights@.map(|j: int, x: i8| x as int)),
            valid_boxes(boxes@.map(|j: int, x: (i8, i8)| (x.0 as int, x.1 as int)), stairs_amount as int),
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] >= 0,
            forall|j: int| 0 <= j < i ==> result@[j] as int >= stair_heights@[0] as int,
            forall|j: int| 0 <= j < i ==> result@[j] as int >= stair_heights@[sub(boxes@[j].0 as int, 1)] as int,
            forall|j: int| 0 <= j < i ==> result@[j] as int == max(if j == 0 { stair_heights@[0] as int } else { result@[sub(j, 1)] as int + boxes@[sub(j, 1)].1 as int }, stair_heights@[sub(boxes@[j].0 as int, 1)] as int),
            i > 0 ==> current_height as int == result@[sub(i as int, 1)] as int + boxes@[sub(i as int, 1)].1 as int,
            i == 0 ==> current_height == 0,
        decreases boxes.len() - i
    {
        let box_stair = boxes[i].0;
        let box_height = boxes[i].1;
        let stair_index = (box_stair - 1) as usize;
        let stair_height = stair_heights[stair_index];
        
        let prev_height = if i == 0 {
            stair_heights[0]
        } else {
            current_height
        };
        
        let new_height = if prev_height >= stair_height {
            prev_height
        } else {
            stair_height
        };
        
        result.push(new_height);
        current_height = new_height + box_height;
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}