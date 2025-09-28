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
/* code modified by LLM (iteration 5): Fixed syntax for tracked mutable variables by adding let keyword */
{
    proof {
        assert(a@.len() == k as int);
    }
    let mut i: usize = 1;
    let mut best_index: usize = 0;
    let mut max_transport_rt: i32 = (a[0] as i32) * ((n as i32) / (a[0] as i32));
    let tracked(mut best_index_ghost: int) = 0;
    let tracked(mut max_transport_ghost: int) = hamsters_transported(n as int, a@[0] as int);
    while i < (k as usize)
        invariant
            0 <= best_index_ghost < a@.len(),
            best_index_ghost < i as int,
            max_transport_ghost == hamsters_transported(n as int, a@[best_index_ghost]),
            forall|j: int| 0 <= j < i ==> #[trigger] hamsters_transported(n as int, a@[best_index_ghost]) >= #[trigger] hamsters_transported(n as int, a@[j]),
        decreases (k as usize) - i
    {
        let capa = a[i];
        let transport_rt: i32 = (capa as i32) * ((n as i32) / (capa as i32));
        let transport_ghost: int = hamsters_transported(n as int, a@[i as int] as int);
        proof {
            assert(transport_rt as int == transport_ghost);
        }
        if transport_rt > max_transport_rt {
            max_transport_rt = transport_rt;
            best_index_ghost = i as int;
            max_transport_ghost = transport_ghost;
            best_index = i;
        }
        i = i + 1;
    }
    let capacity: int = a@[best_index_ghost];
    let num_boxes_value: int = (n as int) / capacity;
    let num_boxes: i8 = num_boxes_value as i8;
    let box_type: i8 = (best_index_ghost as i8) + 1;
    (box_type, num_boxes)
}
// </vc-code>


}

fn main() {}