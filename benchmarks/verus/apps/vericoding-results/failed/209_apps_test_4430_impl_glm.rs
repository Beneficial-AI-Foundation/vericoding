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
/* helper modified by LLM (iteration 4): fix sequence indexing by using normal vector indexing instead of ghost sequence indexing */
fn greedy_pack_recursive(a: &Vec<i32>, pos: i32, boxes_left: i32, capacity: i32, current_box_space: i32) -> (result: i32)
    requires
        capacity >= 1,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i] >= 1 && #[trigger] a@[i] <= capacity,
        boxes_left >= 1,
        0 <= current_box_space <= capacity,
    ensures
        result == greedy_pack_from_end_helper(a@.map(|i, x| x as int), pos as int, boxes_left as int, capacity as int, current_box_space as int),
    decreases (pos + 1) as int,
{
    if pos < 0 {
        0
    } else if (pos as usize) >= a.len() {
        0
    } else {
        let val = a[pos as usize];
        if val > capacity {
            0
        } else if val <= current_box_space {
            1 + greedy_pack_recursive(a, pos - 1, boxes_left, capacity, current_box_space - val)
        } else if boxes_left > 1 {
            1 + greedy_pack_recursive(a, pos - 1, boxes_left - 1, capacity, capacity - val)
        } else {
            0
        }
    }
}

fn greedy_pack_from_end_exec(a: Vec<i32>, boxes: i32, capacity: i32) -> (result: i32)
    requires
        boxes >= 1,
        capacity >= 1,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i] >= 1 && #[trigger] a@[i] <= capacity,
    ensures
        result == greedy_pack_from_end(a@.map(|i, x| x as int), boxes as int, capacity as int),
{
    let len = a.len() as i32;
    greedy_pack_recursive(&a, len - 1, boxes, capacity, capacity)
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
    /* code modified by LLM (iteration 5): replace collect with manual vector construction */
    let mut a_vec = Vec::new();
    for i in 0..a.len() {
        a_vec.push(a[i] as i32);
    }
    let res = greedy_pack_from_end_exec(a_vec, m as i32, k as i32);
    res as i8
}
// </vc-code>


}

fn main() {}