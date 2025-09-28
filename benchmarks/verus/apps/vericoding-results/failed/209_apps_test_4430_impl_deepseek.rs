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

proof fn lemma_greedy_pack_from_end_helper_monotonic(a: Seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space: int, pos2: int)
    requires
        capacity >= 1,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 1 && #[trigger] a[i] <= capacity,
        boxes_left >= 1,
        0 <= current_box_space <= capacity,
        pos2 <= pos,
    ensures
        greedy_pack_from_end_helper(a, pos, boxes_left, capacity, current_box_space) >= greedy_pack_from_end_helper(a, pos2, boxes_left, capacity, current_box_space),
    decreases pos + 1,
{
    if pos < 0 {
    } else if pos >= a.len() {
    } else if a[pos] > capacity {
    } else if a[pos] <= current_box_space {
        lemma_greedy_pack_from_end_helper_monotonic(a, pos - 1, boxes_left, capacity, current_box_space - a[pos], pos2)
    } else if boxes_left > 1 {
        lemma_greedy_pack_from_end_helper_monotonic(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos], pos2)
    } else {
    }
}

proof fn lemma_greedy_pack_from_end_helper_boxes_monotonic(a: Seq<int>, pos: int, boxes_left1: int, boxes_left2: int, capacity: int, current_box_space: int)
    requires
        capacity >= 1,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 1 && #[trigger] a[i] <= capacity,
        boxes_left1 >= 1,
        boxes_left2 >= 1,
        boxes_left1 <= boxes_left2,
        0 <= current_box_space <= capacity,
    ensures
        greedy_pack_from_end_helper(a, pos, boxes_left1, capacity, current_box_space) <= greedy_pack_from_end_helper(a, pos, boxes_left2, capacity, current_box_space),
    decreases pos + 1,
{
    if pos < 0 {
    } else if pos >= a.len() {
    } else if a[pos] > capacity {
    } else if a[pos] <= current_box_space {
        lemma_greedy_pack_from_end_helper_boxes_monotonic(a, pos - 1, boxes_left1, boxes_left2, capacity, current_box_space - a[pos])
    } else if boxes_left1 > 1 {
        lemma_greedy_pack_from_end_helper_boxes_monotonic(a, pos - 1, boxes_left1 - 1, boxes_left2 - 1, capacity, capacity - a[pos])
    } else {
        lemma_greedy_pack_from_end_helper_boxes_monotonic(a, pos - 1, boxes_left1, boxes_left2 - 1, capacity, capacity - a[pos])
    }
}

proof fn lemma_greedy_pack_from_end_helper_space_monotonic(a: Seq<int>, pos: int, boxes_left: int, capacity: int, current_box_space1: int, current_box_space2: int)
    requires
        capacity >= 1,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 1 && #[trigger] a[i] <= capacity,
        boxes_left >= 1,
        0 <= current_box_space1 <= capacity,
        0 <= current_box_space2 <= capacity,
        current_box_space1 <= current_box_space2,
    ensures
        greedy_pack_from_end_helper(a, pos, boxes_left, capacity, current_box_space1) <= greedy_pack_from_end_helper(a, pos, boxes_left, capacity, current_box_space2),
    decreases pos + 1,
{
    if pos < 0 {
    } else if pos >= a.len() {
    } else if a[pos] > capacity {
    } else if a[pos] <= current_box_space1 {
        lemma_greedy_pack_from_end_helper_space_monotonic(a, pos - 1, boxes_left, capacity, current_box_space1 - a[pos], current_box_space2 - a[pos])
    } else if a[pos] <= current_box_space2 {
        lemma_greedy_pack_from_end_helper_boxes_monotonic(a, pos - 1, boxes_left - 1, boxes_left, capacity, capacity - a[pos])
    } else if boxes_left > 1 {
        lemma_greedy_pack_from_end_helper_space_monotonic(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos], capacity - a[pos])
    } else {
    }
}

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
    /* code modified by LLM (iteration 5): fixed compilation error by removing redundant as int cast */
    let mut result: i8 = 0;
    let mut boxes_left = m;
    let mut current_box_space = k;
    let mut pos = (n - 1) as i64;
    
    while pos >= 0 && boxes_left > 0 {
        invariant
            result as int == greedy_pack_from_end_helper(a@.map(|_i, x| x as int), pos as int, boxes_left as int, k as int, current_box_space as int),
            boxes_left >= 0,
            current_box_space >= 0,
            current_box_space <= k,
            pos >= -1,
        decreases (pos + 1) as int,
        
        let item_val = a[pos as usize];
        
        if item_val <= current_box_space {
            current_box_space -= item_val;
            result += 1;
            pos -= 1;
        } else if boxes_left > 1 {
            boxes_left -= 1;
            current_box_space = k - item_val;
            result += 1;
            pos -= 1;
        } else {
            break;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}