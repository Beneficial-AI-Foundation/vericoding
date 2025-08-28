use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
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
{
    let temp_h = a[h];
    let temp_i = a[i];
    let temp_j = a[j];
    
    a.set(h, temp_i);
    a.set(j, temp_h);
    a.set(i, temp_j);
}
// </vc-code>

fn main() {}

}