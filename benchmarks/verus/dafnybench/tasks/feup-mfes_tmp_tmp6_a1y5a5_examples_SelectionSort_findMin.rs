// <vc-preamble>
use vstd::prelude::*;

verus! {

pub open spec fn is_sorted(a: &[i32], from: usize, to: usize) -> bool {
    &&& from <= to <= a.len()
    &&& forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_min(a: &mut [i32], from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= old(a).len(),
    ensures
        from <= index < to,
        forall|k: int| from <= k < to ==> old(a)[k] >= old(a)[index as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}