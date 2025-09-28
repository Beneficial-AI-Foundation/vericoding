// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn greedy_pack_from_end(a: Seq<int>, boxes: int, capacity: int) -> int
    recommends
        boxes >= 1,
        capacity >= 1,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 1 && #[trigger] a[i] <= capacity,
{
    greedy_pack_from_end_helper(a, a.len() - 1, boxes, capacity, capacity)
}

spec fn greedy_pack_from_end_helper(a: Seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int) -> int
    recommends
        capacity >= 1,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 1 && #[trigger] a[i] <= capacity,
        boxes_left >= 1,
        0 <= current_box_space <= capacity,
    decreases pos + 1,
{
    if pos < 0 {
        0int
    } else if pos >= a.len() {
        0int
    } else if a[pos] > capacity {
        0int
    } else if a[pos] <= current_box_space {
        1int + greedy_pack_from_end_helper(a, pos - 1, boxes_left, capacity, current_box_space - a[pos])
    } else if boxes_left > 1 {
        1int + greedy_pack_from_end_helper(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos])
    } else {
        0int
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, k: i8, a: Vec<i8>) -> (result: i8)
    requires
        n >= 0,
        m >= 1,
        k >= 1,
        a.len() == n as usize,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] as int >= 1 && #[trigger] a[i] as int <= k as int,
    ensures
        0 <= result as int <= n as int,
        result as int == greedy_pack_from_end(a@.map(|i, x| x as int), m as int, k as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed invariant maintenance by matching spec exactly */
    if n == 0 {
        return 0;
    }
    
    let mut pos: usize = n as usize;
    let mut boxes_left: i8 = m;
    let mut current_box_space: i8 = k;
    let mut count: i8 = 0;
    
    while pos > 0
        invariant
            n >= 0,
            m >= 1,
            k >= 1,
            a.len() == n as usize,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] as int >= 1 && #[trigger] a[i] as int <= k as int,
            0 <= count as int <= n as int,
            boxes_left >= 1,
            0 <= current_box_space as int <= k as int,
            pos <= n as usize,
            count as int == greedy_pack_from_end(a@.map(|i, x| x as int), m as int, k as int) - greedy_pack_from_end_helper(a@.map(|i, x| x as int), (pos as int) - 1, boxes_left as int, k as int, current_box_space as int),
        decreases pos,
    {
        pos = pos - 1;
        
        if a[pos] <= current_box_space {
            count = count + 1;
            current_box_space = current_box_space - a[pos];
        } else if boxes_left > 1 {
            count = count + 1;
            boxes_left = boxes_left - 1;
            current_box_space = k - a[pos];
        }
    }
    
    count
}
// </vc-code>


}

fn main() {}