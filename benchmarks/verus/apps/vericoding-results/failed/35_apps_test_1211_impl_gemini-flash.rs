// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, a: Seq<int>) -> bool {
    k > 0 && a.len() == k && (forall|i: int| 0 <= i < k ==> #[trigger] a[i] > 0) && n >= 0
}

spec fn hamsters_transported(n: int, capacity: int) -> int {
    if capacity > 0 {
        capacity * (n / capacity)
    } else {
        0
    }
}

spec fn optimal_solution(n: int, a: Seq<int>, box_type: int, num_boxes: int) -> bool {
    valid_input(n, a.len() as int, a) &&
    1 <= box_type <= a.len() &&
    num_boxes == n / a[box_type - 1] &&
    forall|i: int| 0 <= i < a.len() ==> #[trigger] hamsters_transported(n, a[box_type - 1]) >= #[trigger] hamsters_transported(n, a[i])
}
// </vc-preamble>

// <vc-helpers>
spec fn max_hamsters_transported(n: int, a: Seq<int>) -> (capacity_idx: int, max_h: int)
    requires valid_input(n, a.len() as int, a)
    ensures
        0 <= capacity_idx < a.len(),
        max_h == hamsters_transported(n, a[capacity_idx]),
        forall|i: int| 0 <= i < a.len() ==> hamsters_transported(n, a[i]) <= max_h,
{
    if a.len() == 0 {
        // Should not happen given valid_input requires k > 0, so a.len() > 0
        (0, 0)
    } else {
        let mut max_h_so_far: int = 0;
        let mut max_idx_so_far: int = 0;
        let mut i: int = 0;

        while i < a.len()
            invariant
                0 <= i <= a.len(),
                0 <= max_idx_so_far < a.len(),
                max_h_so_far == hamsters_transported(n, a[max_idx_so_far]),
                forall|j: int| 0 <= j < i ==> hamsters_transported(n, a[j]) <= max_h_so_far,
            decreases a.len() - i
        {
            let current_h = hamsters_transported(n, a[i]);
            if current_h >= max_h_so_far {
                max_h_so_far = current_h;
                max_idx_so_far = i;
            }
            i = i + 1;
        }
        (max_idx_so_far, max_h_so_far)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(n as int, k as int, a@.map(|i, x: i8| x as int))
    ensures ({
        let (box_type, num_boxes) = result;
        1 <= box_type <= k &&
        num_boxes >= 0 &&
        optimal_solution(n as int, a@.map(|i, x: i8| x as int), box_type as int, num_boxes as int)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement solve function using max_hamsters_transported helper function */
    let a_seq = a@.map(|i, x: i8| x as int);

    let (best_box_idx, _max_h) = max_hamsters_transported(n as int, a_seq);

    let box_type = (best_box_idx + 1) as i8;
    let num_boxes = (n as int / a_seq[best_box_idx]) as i8;

    (box_type, num_boxes)
}
// </vc-code>


}

fn main() {}