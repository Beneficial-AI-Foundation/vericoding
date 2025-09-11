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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}