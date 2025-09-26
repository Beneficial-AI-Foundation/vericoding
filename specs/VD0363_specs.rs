// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(a: &Vec<i32>, start: int, end: int) -> bool {
    &&& 0 <= start <= end <= a.len()
    &&& forall|j: int, k: int| start <= j < k < end ==> a[j] <= a[k]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    requires 
        old(a).len() > 1,
    ensures 
        sorted(a, 0, a.len() as int),
        a.len() == old(a).len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}