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
/* helper modified by LLM (iteration 4): Properly proved the sum_additivty lemma by revealing the spec function definition and asserting the equality directly from the recursive definition. */
proof fn sum_additivty(a: Seq<i32>, s: int, t: int)
    requires 0 <= s < t <= a.len()
    ensures sum(a, s, t) == sum(a, s, t - 1) + a[t - 1]
{
    reveal(sum);
    assert(sum(a, s, t) == a[t - 1] + sum(a, s, t - 1));
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
    /* code modified by LLM (iteration 5): Fixed compilation errors by correcting tracked variable assignment syntax from .set() to =, fixed type mismatches by casting usize indices to int in proof blocks for sequence indexing, and restructured initialization to avoid index before length check. */
    if a.len() == 0 {
        return (0, 0);
    }
    let mut max_start: usize = 0;
    let mut max_end: usize = 0;
    let mut temp_start: usize = 0;
    let mut max_sum: i32 = a[0];
    let mut current_sum: i32 = a[0];
    let tracked(mut max_sum_track): i32 = a@[0];
    let tracked(mut current_sum_track): i32 = a@[0];
    for i in 1..a.len() {
        let new_current: i32 = if current_sum < 0 {
            a[i]
        } else {
            current_sum + a[i]
        };
        current_sum = new_current;
        proof {
            current_sum_track = if current_sum_track@ < 0 {
                a@[i as int]
            } else {
                current_sum_track@ + a@[i as int]
            };
        }
        if current_sum > max_sum {
            max_sum = current_sum;
            max_start = temp_start;
            max_end = i;
            proof {
                max_sum_track = current_sum_track@;
            }
        }
        if current_sum < 0 {
            temp_start = i + 1;
        }
    }
    if max_sum <= 0 {
        (0, 0)
    } else {
        (max_start, max_end + 1)
    }
}
// </vc-code>

}
fn main() {}