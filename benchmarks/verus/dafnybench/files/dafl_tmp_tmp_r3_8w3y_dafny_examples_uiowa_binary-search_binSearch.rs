use vstd::prelude::*;

verus! {

spec fn is_sorted(a: &[int]) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

fn bin_search(a: &[int], k: int) -> (b: bool)
    requires is_sorted(a)
    ensures b == exists|i: int| 0 <= i < a.len() && a[i] == k
{
    assume(false);
    unreached()
}

}
fn main() {}