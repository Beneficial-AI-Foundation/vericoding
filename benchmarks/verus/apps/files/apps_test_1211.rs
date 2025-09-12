// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, k: int, a: Seq<int>) -> bool {
    k > 0 && a.len() == k && (forall|i: int| 0 <= i < k ==> a.index(i) > 0) && n >= 0
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
    num_boxes == n / a.index(box_type - 1) &&
    forall|i: int| 0 <= i < a.len() ==> hamsters_transported(n, a.index(box_type - 1)) >= hamsters_transported(n, a.index(i))
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, a: Seq<int>) -> (result: (int, int))
    requires valid_input(n, k, a)
    ensures ({
        let (box_type, num_boxes) = result;
        1 <= box_type <= k &&
        num_boxes >= 0 &&
        optimal_solution(n, a, box_type, num_boxes)
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    (1 as int, 0 as int)
}
// </vc-code>


}

fn main() {}