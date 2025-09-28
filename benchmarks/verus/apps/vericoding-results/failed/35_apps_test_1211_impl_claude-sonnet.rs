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
fn lemma_optimal_exists(n: int, a: Seq<int>)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] > 0,
        n >= 0,
    ensures
        exists|best_idx: int| 0 <= best_idx < a.len() && 
        forall|i: int| 0 <= i < a.len() ==> hamsters_transported(n, a[best_idx]) >= hamsters_transported(n, a[i])
{
}

fn find_best_box(n: i8, a: Vec<i8>) -> (result: i8)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i] > 0,
        n >= 0,
    ensures
        0 <= result < a.len(),
        forall|i: int| 0 <= i < a.len() ==> hamsters_transported(n as int, a@[result as int] as int) >= hamsters_transported(n as int, a@[i] as int)
{
    /* helper modified by LLM (iteration 5): moved ghost computations to proof blocks */
    let mut best_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= best_idx < a.len(),
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> hamsters_transported(n as int, a@[best_idx as int] as int) >= hamsters_transported(n as int, a@[j] as int),
        decreases a.len() - i
    {
        proof {
            let current_transported = hamsters_transported(n as int, a@[i as int] as int);
            let best_transported = hamsters_transported(n as int, a@[best_idx as int] as int);
        }
        
        let current_capacity = a[i];
        let best_capacity = a[best_idx];
        let current_boxes = if current_capacity > 0 { n / current_capacity } else { 0 };
        let best_boxes = if best_capacity > 0 { n / best_capacity } else { 0 };
        let current_transported_exec = current_capacity * current_boxes;
        let best_transported_exec = best_capacity * best_boxes;
        
        if current_transported_exec > best_transported_exec {
            best_idx = i;
        }
        i += 1;
    }
    
    best_idx as i8
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
    /* code modified by LLM (iteration 5): removed direct hamsters_transported call to avoid ghost type usage */
    let best_idx = find_best_box(n, a);
    let box_type = best_idx + 1;
    let capacity = a[best_idx as usize];
    let num_boxes = n / capacity;
    
    (box_type, num_boxes)
}
// </vc-code>


}

fn main() {}