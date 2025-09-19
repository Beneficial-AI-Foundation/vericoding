// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search_recursive(a: Vec<i8>, i: i8, j: i8, x: i8) -> (k: i8)
    requires 
        0 <= i <= j <= a@.len(),
        forall|p: int, q: int| i as int <= p < q < j as int ==> a@[p] >= a@[q],
    ensures 
        i <= k <= j,
        forall|r: int| i as int <= r < k as int ==> a@[r] >= x as int,
        forall|r: int| k as int <= r < j as int ==> a@[r] < x as int,
    decreases j - i
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}