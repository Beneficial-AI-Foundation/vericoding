use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let old_seq: Seq<i32> = a@;
    let old_len: nat = old_seq.len();

    let mut b: Vec<i32> = Vec::new();
    let mut i: nat = 0;

    while i < old_len
        invariant i <= old_len;
        invariant b.len() == i;
        invariant forall |k: int| 0 <= k && k < (i as int) ==> b@[k] == if old_seq@[k] == x { y } else { old_seq@[k] };
    {
        let v: i32 = old_seq@[i as int];
        if v == x {
            b.push(y);
        } else {
            b.push(v);
        }
        i = i + 1;
    }

    // move b into *a
    *a = b;

    // final assertions to help verifier
    assert(a.len() == old_len);
    assert(forall |k: int| 0 <= k && k < (old_len as int) ==>
        a@[k] == if old_seq@[k] == x { y } else { old_seq@[k] });
}
// </vc-code>

fn main() {}
}