use vstd::prelude::*;

verus! {

// <vc-helpers>
fn old_vec_to_seq<T>(v: &Vec<T>) -> vstd::seq::Seq<T> {
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

    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            a.len() == old_a_seq.len(),
            forall|k: int| 0 <= k && (k as usize) < i && #[trigger] old_a_seq.index(k) == x ==> #[trigger] a.index(k) == y,
            forall|k: int| 0 <= k && (k as usize) < i && #[trigger] old_a_seq.index(k) != x ==> #[trigger] a.index(k) == old_a_seq.index(k),
            forall|k: int| (i as int) <= k && (k as usize) < a.len() ==> #[trigger] a.index(k) == old_a_seq.index(k),
    {
        if a[i] == x {
            a.set(i, y);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}
}