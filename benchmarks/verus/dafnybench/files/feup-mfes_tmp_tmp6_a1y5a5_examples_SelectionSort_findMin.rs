use vstd::prelude::*;

verus! {

pub open spec fn is_sorted(a: &[i32], from: usize, to: usize) -> bool {
    &&& from <= to <= a.len()
    &&& forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

fn find_min(a: &mut [i32], from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= old(a).len(),
    ensures
        from <= index < to,
        forall|k: int| from <= k < to ==> old(a)[k] >= old(a)[index as int],
{
    assume(false);
    unreached()
}

}
fn main() {}