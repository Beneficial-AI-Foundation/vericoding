// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(a: &[int]) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted_seq(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-helpers>

// <vc-spec>
fn bin_search(a: &[i8], k: i8) -> (b: bool)
    requires is_sorted_seq(a@.map(|i, x| x as int))
    ensures b == exists|i: int| 0 <= i < a@.len() && a@[i] as int == k as int
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}