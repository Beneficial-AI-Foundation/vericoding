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
{
    /* code modified by LLM (iteration 5): Fixed loop invariants for proper verification */
    let mut max_sum: i64 = 0;
    let mut best_i: usize = 0;
    let mut best_j: usize = 0;
    
    let mut i: usize = 0;
    while i <= a.len()
        invariant
            i <= a.len() + 1,
            best_i <= best_j <= a.len(),
            forall|k: int, l: int| 0 <= k <= l <= j_max(i as int) ==> sum(a@, k, l) <= sum(a@, best_i as int, best_j as int),
            max_sum == sum(a@, best_i as int, best_j as int) as i64,
        decreases a.len() + 1 - i,
    {
        let mut j: usize = i;
        let mut current_sum: i64 = 0;
        
        proof {
            assert(sum(a@, i as int, i as int) == 0);
        }
        
        while j <= a.len()
            invariant
                i <= j <= a.len() + 1,
                best_i <= best_j <= a.len(),
                current_sum == sum(a@, i as int, j as int) as i64,
                forall|k: int, l: int| 0 <= k <= l <= j_max(i as int) ==> sum(a@, k, l) <= sum(a@, best_i as int, best_j as int),
                forall|l: int| i <= l < j ==> sum(a@, i as int, l as int) <= sum(a@, best_i as int, best_j as int),
                max_sum == sum(a@, best_i as int, best_j as int) as i64,
            decreases a.len() + 1 - j,
        {
            if current_sum > max_sum {
                max_sum = current_sum;
                best_i = i;
                best_j = j;
            }
            
            if j < a.len() {
                current_sum = current_sum + (a[j] as i64);
            }
            j = j + 1;
        }
        
        i = i + 1;
    }
    
    (best_i, best_j)
}

spec fn j_max(i: int) -> int {
    if i == 0 { 0 } else { a.len() as int }
}
// </vc-code>

}
fn main() {}