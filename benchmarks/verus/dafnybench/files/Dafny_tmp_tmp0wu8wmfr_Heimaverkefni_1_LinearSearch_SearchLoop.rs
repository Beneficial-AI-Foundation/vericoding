// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search_loop(a: &Vec<i32>, i: usize, j: usize, x: i32) -> (k: i32)
    requires 
        i <= j <= a.len(),
    ensures 
        (i <= k < j) || k == -1,
        k != -1 ==> 0 <= k < a.len() && a[k as int] == x,
        k != -1 ==> forall|r: int| k < r < j && 0 <= r < a.len() ==> a[r] != x,
        k == -1 ==> forall|r: int| (i as int) <= r < (j as int) && 0 <= r < a.len() ==> a[r] != x,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}