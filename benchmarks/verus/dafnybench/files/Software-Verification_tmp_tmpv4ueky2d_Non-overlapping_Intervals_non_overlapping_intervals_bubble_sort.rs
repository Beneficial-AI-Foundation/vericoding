// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: &Vec<(i32, i32)>, l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i].1 <= a[j].1
}

spec fn partitioned(a: &Vec<(i32, i32)>, i: int) -> bool {
    forall|k: int, k_prime: int| 0 <= k <= i < k_prime < a.len() ==> a[k].1 <= a[k_prime].1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<(i32, i32)>)
    ensures sorted(a, 0, a.len() as int - 1)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}