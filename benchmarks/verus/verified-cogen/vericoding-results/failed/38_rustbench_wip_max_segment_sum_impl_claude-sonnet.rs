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
/* helper modified by LLM (iteration 5): removed helper functions to avoid compilation issues */
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_segment_sum(a: &Vec<i32>, s: usize, t: usize) -> (p: (usize, usize)) by (nonlinear_arith)
    ensures
        ({ let (i, j) = p; 0 <= i <= j <= a.len() }),
        ({ let (i, j) = p; forall|k: int, l: int| 0 <= k <= l <= a.len() ==> sum(a@, k, l) <= sum(a@, i as int, j as int) })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by keeping max_sum as ghost variable */
    let mut best_i = 0;
    let mut best_j = 0;
    ghost let mut max_sum = 0;
    
    let mut i = 0;
    while i <= a.len()
        invariant
            0 <= i <= a.len(),
            0 <= best_i <= best_j <= a.len(),
            forall|k: int, l: int| 0 <= k <= l <= i ==> sum(a@, k, l) <= sum(a@, best_i as int, best_j as int),
    {
        let mut j = i;
        while j <= a.len()
            invariant
                i <= j <= a.len(),
                0 <= best_i <= best_j <= a.len(),
                forall|k: int, l: int| (0 <= k <= l <= i) || (i <= k <= l <= j) ==> sum(a@, k, l) <= sum(a@, best_i as int, best_j as int),
        {
            proof {
                let current_sum = sum(a@, i as int, j as int);
                if current_sum > max_sum {
                    max_sum = current_sum;
                    best_i = i;
                    best_j = j;
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    (best_i, best_j)
}
// </vc-code>

}
fn main() {}