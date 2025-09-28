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
fn hamsters_transported_helper(n: int, capacity: int) -> int {
    if capacity > 0 {
        capacity * (n / capacity)
    } else {
        0
    }
}

fn find_optimal_box_type(n: int, a: Seq<int>) -> (best_index: int)
    requires valid_input(n, a.len() as int, a)
    ensures 0 <= best_index < a.len() &&
        forall|i: int| 0 <= i < a.len() ==> hamsters_transported_helper(n, a[best_index]) >= hamsters_transported_helper(n, a[i])
{
    let mut best_index = 0;
    let mut max_transported = hamsters_transported_helper(n, a[0]);
    let mut i = 1;
    
    while i < a.len()
        invariant 0 <= best_index < a.len() &&
                   1 <= i <= a.len() &&
                   max_transported == hamsters_transported_helper(n, a[best_index]) &&
                   forall|j: int| 0 <= j < i ==> hamsters_transported_helper(n, a[best_index]) >= hamsters_transported_helper(n, a[j])
        decreases a.len() - i
    {
        let current_transported = hamsters_transported_helper(n, a[i]);
        if current_transported > max_transported {
            best_index = i;
            max_transported = current_transported;
        }
        i = i + 1;
    }
    
    best_index
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
    let n_int = n as int;
    let a_seq = a@.map(|i, x: i8| x as int);
    
    let best_index = find_optimal_box_type(n_int, a_seq);
    let box_type = (best_index + 1) as i8;
    let capacity = a_seq[best_index];
    let num_boxes = (n_int / capacity) as i8;
    
    (box_type, num_boxes)
}
// </vc-code>


}

fn main() {}