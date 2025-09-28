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
    let mut best_type: i8 = 1;
    let mut best_count: i8 = 0;
    let mut i: usize = 0;
    
    while i < k as usize
        invariant
            0 <= i <= k as usize,
            k > 0,
            a.len() == k as usize,
            1 <= best_type <= k,
            best_count == (n / a[(best_type - 1) as usize]) as i8,
            forall|j: int| 0 <= j < i ==> hamsters_transported(n as int, a@[(best_type - 1) as int] as int) >= hamsters_transported(n as int, a@[j] as int),
            forall|j: int| 0 <= j < a.len() ==> a@[j] > 0,
            n >= 0,
    {
        let current_count = (n / a[i]) as i8;
        if current_count * a[i] > best_count * a[(best_type - 1) as usize] {
            best_type = (i + 1) as i8;
            best_count = current_count;
        }
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < a.len() ==> hamsters_transported(n as int, a@[(best_type - 1) as int] as int) >= hamsters_transported(n as int, a@[j] as int));
    
    (best_type, best_count)
}
// </vc-code>


}

fn main() {}