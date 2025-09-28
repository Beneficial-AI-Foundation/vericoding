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
proof fn lemma_segment_max(a: Seq<i32>, k: int, l: int, i: int, j: int)
    requires
        0 <= k <= l <= a.len(),
        0 <= i <= j <= a.len(),
        sum(a, k, l) <= sum(a, i, j),
        forall|p: int, q: int| 0 <= p <= q <= a.len() ==> sum(a, p, q) <= sum(a, i, j)
    ensures
        forall|p: int, q: int| 0 <= p <= q <= a.len() ==> sum(a, p, q) <= sum(a, i, j)
{
}

proof fn ghost_max_sum_helper(a: Seq<i32>, i: int, j: int, max_value: int)
    requires
        0 <= i <= j <= a.len(),
        sum(a, i, j) == max_value,
        forall|k: int, l: int| 0 <= k <= l <= a.len() ==> sum(a, k, l) <= max_value
    ensures
        forall|k: int, l: int| 0 <= k <= l <= a.len() ==> sum(a, k, l) <= sum(a, i, j)
{
}

proof fn lemma_transitive_max(a: Seq<i32>, max_value: int, i: int, j: int)
    requires
        0 <= i <= j <= a.len(),
        sum(a, i, j) == max_value,
        forall|k: int, l: int| 0 <= k <= l <= a.len() ==> sum(a, k, l) <= max_value
    ensures
        forall|k: int, l: int| 0 <= k <= l <= a.len() ==> sum(a, k, l) <= sum(a, i, j)
{
}
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
    /* code modified by LLM (iteration 5): Added decreases clause to fix verification error */
    let mut max_sum: i32 = 0;
    let mut max_i = s;
    let mut max_j = s;
    
    let mut current_sum: i32 = 0;
    let mut current_start = s;
    
    let mut idx = s;
    
    while idx < t
        decreases t - idx,
        invariant
            s <= idx <= t,
            current_sum >= 0,
            s <= current_start <= idx,
            max_i <= max_j <= idx,
            s <= max_i <= max_j <= idx,
            sum(a@, max_i as int, max_j as int) == max_sum as int,
            forall|k: int, l: int| s as int <= k <= l <= idx as int ==> sum(a@, k, l) <= max_sum as int
    {
        current_sum += a[idx];
        
        if current_sum < 0 {
            current_sum = 0;
            current_start = idx + 1;
        }
        
        proof {
            let ghost_current_sum = current_sum as int;
            let ghost_max_sum = max_sum as int;
            
            if ghost_current_sum > ghost_max_sum {
                ghost_max_sum_helper(a@, current_start as int, (idx + 1) as int, ghost_current_sum);
            }
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            max_i = current_start;
            max_j = idx + 1;
        }
        
        idx += 1;
    }
    
    (max_i, max_j)
}
// </vc-code>

}
fn main() {}