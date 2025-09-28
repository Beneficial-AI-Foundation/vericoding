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
proof fn lemma_valid_stairs_non_decreasing(stair_heights: Seq<int>) 
    requires valid_stairs(stair_heights), 
    ensures forall|i: int, j: int| 0 <= i <= j < stair_heights.len() ==> #[trigger] stair_heights[i] <= #[trigger] stair_heights[j]
{
    if stair_heights.len() == 0 {
        return;
    }
    
    let n = stair_heights.len();
    
    proof {
        assert forall|k: int| 0 <= k < n - 1 implies stair_heights[k] <= stair_heights[add(k, 1)] by {
            assert(valid_stairs(stair_heights));
        };
        
        assert forall|i: int, j: int| 0 <= i <= j < n implies #[trigger] stair_heights[i] <= #[trigger] stair_heights[j] by {
            if i == j {
                assert(stair_heights[i] <= stair_heights[j]);
            } else {
                assert(j >= i + 1);
                let mut k = i;
                while k < j 
                    invariant i <= k <= j, 
                             stair_heights[i] <= stair_heights[k]
                    decreases j - k
                {
                    assert(stair_heights[k] <= stair_heights[add(k, 1)]);
                    assert(stair_heights[i] <= stair_heights[add(k, 1)]);
                    k = k + 1;
                }
                assert(stair_heights[i] <= stair_heights[j]);
            }
        };
    }
}

proof fn lemma_max_properties(a: int, b: int) 
    ensures max(a, b) >= a, 
             max(a, b) >= b, 
             max(a, b) == a || max(a, b) == b
{
    if a >= b {
        assert(max(a, b) == a);
        assert(max(a, b) >= a);
        assert(max(a, b) >= b);
    } else {
        assert(max(a, b) == b);
        assert(max(a, b) >= a);
        assert(max(a, b) >= b);
    }
}

proof fn lemma_transitivity_le(x: int, y: int, z: int) 
    requires x <= y, y <= z 
    ensures x <= z 
{
}

/* helper modified by LLM (iteration 5): Removed int conversions in ghost-only helpers */
proof fn lemma_seq_index_syntax() {
    let s = seq![(1, 2), (3, 4)];
    assert(s[0].1 == 2);
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
    /* code modified by LLM (iteration 5): Fixed compilation error by moving sequence mapping to ghost blocks */
    let mut result: Vec<i8> = Vec::new();
    
    if boxes_amount == 0 {
        proof {
            assert(valid_result(result@.map(|i: int, x: i8| x as int), boxes@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int)), stair_heights@.map(|i: int, x: i8| x as int)));
        }
        return result;
    }
    
    proof {
        let sh_ints = stair_heights@.map(|i: int, x: i8| x as int);
        let boxes_ints = boxes@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int));
        
        lemma_valid_stairs_non_decreasing(sh_ints);
        lemma_seq_index_syntax();
    }
    
    let mut prev_height = stair_heights[0];
    
    for i in 0..boxes_amount as usize {
        let box_info = boxes[i];
        let stair_idx = (box_info.0 - 1) as usize;
        let required_height = stair_heights[stair_idx];
        
        let candidate1 = if i == 0 { stair_heights[0] } else { prev_height + boxes[i - 1].1 };
        let current_height = if candidate1 >= required_height { candidate1 } else { required_height };
        
        proof {
            let sh_ints = stair_heights@.map(|i: int, x: i8| x as int);
            let boxes_ints = boxes@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int));
            let i_int = i as int;
            let stored_result_seq = result@.map(|i: int, x: i8| x as int);
            let current_height_int = current_height as int;
            
            lemma_max_properties(candidate1 as int, required_height as int);
            
            if i_int > 0 {
                let prev_height_int = prev_height as int;
                let box_prev_second_int = boxes[i - 1].1 as int;
                
                assert(stored_result_seq[i_int - 1] == prev_height_int);
                assert(prev_height_int >= sh_ints[0]);
                assert(prev_height_int >= sh_ints[boxes_ints[i_int - 1].0 - 1]);
                
                assert(boxes_ints[i_int - 1].1 == box_prev_second_int);
                assert(candidate1 as int == prev_height_int + box_prev_second_int);
            }
            
            assert(current_height_int >= sh_ints[stair_idx as int]);
            if i_int == 0 {
                assert(current_height_int >= sh_ints[0]);
            } else {
                assert(current_height_int >= stored_result_seq[sub(i_int, 1)] + boxes_ints[sub(i_int, 1)].1);
            }
        }
        
        result.push(current_height);
        prev_height = current_height;
    }
    
    proof {
        let result_ints = result@.map(|i: int, x: i8| x as int);
        let boxes_ints = boxes@.map(|i: int, x: (i8, i8)| (x.0 as int, x.1 as int));
        let sh_ints = stair_heights@.map(|i: int, x: i8| x as int);
        assert(valid_result(result_ints, boxes_ints, sh_ints));
    }
    
    result
}
// </vc-code>


}

fn main() {}