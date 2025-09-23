// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap3(a: &mut Vec<i32>, h: usize, i: usize, j: usize)
    requires 
        h < old(a).len(),
        i < old(a).len(),
        j < old(a).len(),
        i != j && j != h && h != i,
    ensures
        a[h as int] == old(a)[i as int],
        a[j as int] == old(a)[h as int],
        a[i as int] == old(a)[j as int],
        forall|k: int| 0 <= k < old(a).len() && k != h as int && k != i as int && k != j as int ==> a[k] == old(a)[k],
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