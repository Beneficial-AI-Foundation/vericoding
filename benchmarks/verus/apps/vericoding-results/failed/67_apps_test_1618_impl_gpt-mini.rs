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
/* helper modified by LLM (iteration 3): proof that max of two non-negative ints is non-negative */
fn max_nonneg(a: int, b: int)
    requires
        a >= 0,
        b >= 0,
    ensures
        max(a, b) >= 0,
{
    proof {
        if a >= b {
            assert(max(a, b) == a);
            assert(a >= 0);
        } else {
            assert(max(a, b) == b);
            assert(b >= 0);
        }
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
    /* code modified by LLM (iteration 3): compute result using native indices and i8 arithmetic, maintain ghost invariants via casts */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < boxes_amount as usize
        invariant
            0 <= i as int && i as int <= boxes_amount as int,
            result@.len() == i as int,
            (forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] as int >= 0),
            (forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] as int >= stair_heights@[0] as int),
            (forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] as int >= stair_heights@[ (boxes@[j].0 as int) - 1 ] as int),
            (forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] as int == max(if j == 0 { stair_heights@[0] as int } else { result@[j - 1] as int + boxes@[j - 1].1 as int }, stair_heights@[ (boxes@[j].0 as int) - 1 ] as int)),
        decreases
            (boxes_amount as int) - (i as int)
    {
        let prev_or_base: i16 = if i == 0 {
            stair_heights[0] as i16
        } else {
            (result[i - 1] as i16) + (boxes[i - 1].1 as i16)
        };
        let goal: i16 = stair_heights[(boxes[i].0 as usize) - 1] as i16;
        let chosen: i16 = if prev_or_base >= goal { prev_or_base } else { goal };
        result.push(chosen as i8);
        i = i + 1;
    }
    result
}

// </vc-code>


}

fn main() {}