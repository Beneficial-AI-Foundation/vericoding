// <vc-preamble>
#![crate_name = "max_segment_sum"]

use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<i32>, s: int, t: int) -> int
    decreases t - s,
{
    if s < 0 || s >= t || t > a.len() {
        0
    } else {
        a[t - 1] + sum(a, s, t - 1)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_segment_sum(a: &Vec<i32>, s: usize, t: usize) -> (p: (usize, usize)) by (nonlinear_arith)
    ensures
        ({ let (i, j) = p; 0 <= i <= j <= a.len() }),
        ({ let (i, j) = p; forall|k: int, l: int| 0 <= k <= l <= a.len() ==> sum(a@, k, l) <= sum(a@, i as int, j as int) })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the loop invariants related to `max_so_far` and `current_max` to reflect the Kadane's algorithm logic correctly. Explicitly handled the initial condition where `max_so_far` might be updated inside the loop. The `assert(s==0 && t==n)` was removed as it's not universally true for `max_segment_sum`. */
{
    let n = a.len();
    if n == 0 {
        return (0, 0);
    }

    let mut max_so_far: i32 = a[0]; // Initialize with the first element, as Kadane's can start with negative values
    let mut current_max: i32 = 0;
    let mut start_idx: usize = 0;
    let mut end_idx: usize = 1; // If max_so_far is a[0], the segment is [0, 1)
    let mut current_start: usize = 0;
    
    // Handle the case where the first element is the max segment.
    // This ensures that `max_so_far` is initialized correctly for non-empty arrays.
    proof {
        if n > 0 {
            // The initial state before the loop needs to satisfy the invariants.
            // If n > 0, max_so_far is a[0], start_idx is 0, end_idx is 1.
            // current_max is 0, current_start is 0.
            // We need to ensure that the initial max_so_far is correctly represented.
            // The loop will correctly update it.
        }
    }

    let mut i: usize = 0;
    while i < n
        invariant n == a.len(),
        0 <= i <= n,
        0 <= start_idx <= end_idx <= n,
        0 <= current_start <= i,
        current_max == sum(a@, current_start as int, i as int),
        forall|k: int, l: int| 0 <= k <= l <= i && (k < current_start || l <= current_start || current_start == i) ==> sum(a@, k, l) <= current_max as int,
        forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a@, k, l) <= max_so_far as int,
        max_so_far == sum(a@, start_idx as int, end_idx as int),
        decreases n - i,

    {
        current_max = current_max + a[i];

        if max_so_far < current_max {
            max_so_far = current_max;
            start_idx = current_start;
            end_idx = i + 1;
        }

        if current_max < 0 {
            current_max = 0;
            current_start = i + 1;
        }
        
        i = i + 1;
    }

    (start_idx, end_idx)
}
// </vc-code>

}
fn main() {}