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
/* helper modified by LLM (iteration 5): spec function to convert Vec<i8> to Seq<int> */
spec fn seq_from_vec(a: Vec<i8>) -> Seq<int>
{
    a@.map(|_, x: i8| x as int)
}

/* helper modified by LLM (iteration 5): spec helper for transported hamsters at index */
spec fn transported_of_index(n: int, a: Seq<int>, idx: int) -> int
    requires
        0 <= idx < a.len(),
    ensures
        result == if a@[idx] > 0 { hamsters_transported(n, a@[idx]) } else { 0 },
{
    if a@[idx] > 0 {
        hamsters_transported(n, a@[idx])
    } else {
        0
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
/* code modified by LLM (iteration 5): use ghost variables for spec-level values and mirror ghost updates during runtime search */
{
    // Ghost/spec-level representations
    ghost { let seq_a: Seq<int> = a@.map(|_, x: i8| x as int); }
    ghost { let k_int: int = k as int; }
    ghost { let n_int: int = n as int; }
    ghost { let mut best_idx: int = 0; }
    ghost { let mut best_val_int: int = if seq_a@[0] > 0 { hamsters_transported(n_int, seq_a@[0]) } else { 0 }; }

    // Runtime/executable counterparts
    let mut best_idx_usize: usize = 0usize;
    let cap0: i32 = a[0] as i32;
    let mut best_val_i32: i32 = if cap0 > 0 { cap0 * ((n as i32) / cap0) } else { 0 };

    let mut i: usize = 1usize;
    while i < (k as usize)
        invariant
            0 <= i as int,
            (i as int) <= k_int,
            0 <= best_idx,
            best_idx < k_int,
            best_val_int == if seq_a@[best_idx] > 0 { hamsters_transported(n_int, seq_a@[best_idx]) } else { 0 },
            forall|j: int| 0 <= j < i as int ==> best_val_int >= if seq_a@[j] > 0 { hamsters_transported(n_int, seq_a@[j]) } else { 0 },
        decreases k_int - (i as int)
    {
        let cap: i32 = a[i] as i32;
        let cur: i32 = if cap > 0 { cap * ((n as i32) / cap) } else { 0 };
        if cur > best_val_i32 {
            best_val_i32 = cur;
            best_idx_usize = i;
            ghost {
                best_idx = i as int;
                best_val_int = if seq_a@[best_idx] > 0 { hamsters_transported(n_int, seq_a@[best_idx]) } else { 0 };
            }
        }
        i = i + 1;
    }

    let box_type: i8 = (best_idx_usize + 1) as i8;
    let chosen_cap: i32 = a[best_idx_usize] as i32;
    let num_boxes_i32: i32 = if chosen_cap > 0 { (n as i32) / chosen_cap } else { 0 };
    let num_boxes: i8 = num_boxes_i32 as i8;
    (box_type, num_boxes)
}

// </vc-code>


}

fn main() {}