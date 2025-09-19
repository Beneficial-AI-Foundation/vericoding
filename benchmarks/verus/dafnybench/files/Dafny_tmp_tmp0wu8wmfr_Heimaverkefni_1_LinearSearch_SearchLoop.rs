// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search_loop(a: &Vec<i8>, i: usize, j: usize, x: i8) -> (k: i8)
    requires 
        i <= j <= a.len(),
    ensures 
        (i <= (k as int) < j) || k == -1,
        k != -1 ==> 0 <= (k as int) < a.len() && a[k as int] == x,
        k != -1 ==> forall|r: int| (k as int) < r < j && 0 <= r < a.len() ==> a[r] != x,
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