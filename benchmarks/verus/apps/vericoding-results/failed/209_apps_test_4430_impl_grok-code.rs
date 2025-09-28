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
/* helper modified by LLM (iteration 5): fixed return type naming for ensures clauses */
fn greedy_pack_from_end_helper_exec(a: &Vec<i8>, pos: i32, boxes_left: i8, capacity: i8, current_box_space: i8) -> (result: i8)
    requires
        boxes_left >= 1,
        capacity >= 1,
        0 <= current_box_space <= capacity,
        -1 <= pos < a.len() as i32,
        forall |i: int| 0 <= i < a.len() ==> a[i] >= 1 && a[i] <= capacity,
    ensures
        result as int == greedy_pack_from_end_helper(a@.map(|i, x| x as int), pos, boxes_left as int, capacity as int, current_box_space as int),
    decreases pos + 1,
{
    if pos < 0 {
        0
    } else if pos >= a.len() as i32 {
        0
    } else if a[pos as usize] > capacity {
        0
    } else if a[pos as usize] <= current_box_space {
        1 + greedy_pack_from_end_helper_exec(a, pos - 1, boxes_left, capacity, current_box_space - a[pos as usize])
    } else if boxes_left > 1 {
        1 + greedy_pack_from_end_helper_exec(a, pos - 1, boxes_left - 1, capacity, capacity - a[pos as usize])
    } else {
        0
    }
}

/* helper modified by LLM (iteration 5): fixed return type naming for ensures clauses */
fn greedy_pack_from_end_exec(a: &Vec<i8>, boxes: i8, capacity: i8) -> (result: i8)
    requires
        boxes >= 1,
        capacity >= 1,
        forall |i: int| 0 <= i < a.len() ==> a[i] >= 1 && a[i] <= capacity,
    ensures
        result as int == greedy_pack_from_end(a@.map(|i, x| x as int), boxes as int, capacity as int),
{
    if a.len() == 0 {
        0
    } else {
        greedy_pack_from_end_helper_exec(a, (a.len() - 1) as i32, boxes, capacity, capacity)
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
    /* code modified by LLM (iteration 5): unchanged */
    greedy_pack_from_end_exec(&a, m, k)
}
// </vc-code>


}

fn main() {}