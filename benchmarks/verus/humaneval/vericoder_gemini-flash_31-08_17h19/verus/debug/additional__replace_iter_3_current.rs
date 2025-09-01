use vstd::prelude::*;

verus! {

// <vc-helpers>
fn old_vec_to_seq<T>(v: &Vec<T>) -> vstd::seq::Seq<T>
    ensures
        v.len() == result.len(),
        forall|i: int| 0 <= i && (i as nat) < v.len() ==> result.index(i) == v.index(i),
{
    v.view()
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn replace(a: &mut Vec<i32>, x: i32, y: i32)
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] == x ==> a[k] == y,
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] != x ==> a[k] == old(a)[k],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let old_a_seq = old(a).view();

    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            a.len() == old_a_seq.len(),
            forall|k: int| 0 <= k < i && old_a_seq.index(k) == x ==> a.index(k) == y,
            forall|k: int| 0 <= k < i && old_a_seq.index(k) != x ==> a.index(k) == old_a_seq.index(k),
            forall|k: int| i <= k && (k as nat) < a.len() ==> a.index(k) == old_a_seq.index(k),
    {
        if a[i as nat] == x {
            a.set(i as nat, y);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}
}