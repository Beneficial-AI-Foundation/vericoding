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
/* helper modified by LLM (iteration 5): added proof body to establish postconditions */
proof fn lemma_max_properties(a: int, b: int)
    ensures max(a, b) >= a,
            max(a, b) >= b,
            max(a, b) == a || max(a, b) == b
{
}

proof fn lemma_valid_result_step(result: Seq<int>, boxes: Seq<(int, int)>, stair_heights: Seq<int>, i: int, new_val: int)
    requires
        stair_heights.len() >= 1,
        i >= 0,
        i < boxes.len(),
        forall|j: int| 0 <= j < boxes.len() ==> boxes[j].0 >= 1 && boxes[j].0 <= stair_heights.len(),
        result.len() == i,
        forall|j: int| 0 <= j < i ==> result[j] >= 0,
        forall|j: int| 0 <= j < i ==> result[j] >= stair_heights[0] && result[j] >= stair_heights[sub(boxes[j].0, 1)],
        forall|j: int| 0 <= j < i ==> result[j] == max(if j == 0 { stair_heights[0] } else { result[sub(j, 1)] + boxes[sub(j, 1)].1 }, stair_heights[sub(boxes[j].0, 1)]),
        new_val == max(if i == 0 { stair_heights[0] } else { result[sub(i, 1)] + boxes[sub(i, 1)].1 }, stair_heights[sub(boxes[i].0, 1)])
    ensures
        new_val >= 0,
        new_val >= stair_heights[0],
        new_val >= stair_heights[sub(boxes[i].0, 1)]
{
    lemma_max_properties(if i == 0 { stair_heights[0] } else { result[sub(i, 1)] + boxes[sub(i, 1)].1 }, stair_heights[sub(boxes[i].0, 1)]);
    
    proof {
        if i == 0 {
            assert(new_val >= stair_heights[0]);
            assert(new_val >= 0);
        } else {
            assert(result[sub(i, 1)] >= 0);
            assert(boxes[sub(i, 1)].1 >= 1);
            assert(result[sub(i, 1)] + boxes[sub(i, 1)].1 >= 1);
            assert(new_val >= result[sub(i, 1)] + boxes[sub(i, 1)].1);
            assert(new_val >= stair_heights[0]);
            assert(new_val >= 0);
        }
        assert(new_val >= stair_heights[sub(boxes[i].0, 1)]);
    }
}
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
    /* code modified by LLM (iteration 5): fixed syntax error in assert statement */
    let mut result: Vec<i8> = Vec::new();
    
    let mut i: usize = 0;
    while i < boxes.len()
        invariant
            i <= boxes.len(),
            result.len() == i,
            stairs_amount >= 1,
            stair_heights.len() == stairs_amount as int,
            boxes.len() == boxes_amount as int,
            valid_stairs(stair_heights@.map(|j: int, x: i8| x as int)),
            valid_boxes(boxes@.map(|j: int, x: (i8, i8)| (x.0 as int, x.1 as int)), stairs_amount as int),
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
            forall|j: int| 0 <= j < i ==> 0 <= boxes@[j].0 - 1 < stair_heights.len(),
            forall|j: int| 0 <= j < i ==> result@[j] >= stair_heights@[0] as int && result@[j] >= stair_heights@[boxes@[j].0 as int - 1] as int,
            forall|j: int| 0 <= j < i ==> result@[j] == max(if j == 0 { stair_heights@[0] as int } else { result@[j - 1] + boxes@[j - 1].1 as int }, stair_heights@[boxes@[j].0 as int - 1] as int)
        decreases boxes.len() - i
    {
        let box_stair = boxes[i].0;
        let box_height = boxes[i].1;
        
        assert(box_stair >= 1 && box_stair <= stairs_amount);
        assert((box_stair - 1) as usize < stair_heights.len() as usize);
        
        let from_prev = if i == 0 {
            stair_heights[0]
        } else {
            assert(i > 0);
            assert(i - 1 < result.len());
            result[i - 1] + boxes[i - 1].1
        };
        
        let from_stair = stair_heights[(box_stair - 1) as usize];
        
        let new_height = if from_prev >= from_stair {
            from_prev
        } else {
            from_stair
        };
        
        proof {
            lemma_valid_result_step(
                result@.map(|j: int, x: i8| x as int),
                boxes@.map(|j: int, x: (i8, i8)| (x.0 as int, x.1 as int)),
                stair_heights@.map(|j: int, x: i8| x as int),
                i as int,
                new_height as int
            );
        }
        
        result.push(new_height);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}