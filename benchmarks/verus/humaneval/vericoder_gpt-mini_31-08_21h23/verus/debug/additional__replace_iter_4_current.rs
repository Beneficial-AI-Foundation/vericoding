use vstd::prelude::*;

verus! {

// <vc-helpers>
// Added no helpers; kept minimal to rely on Seq::from_fn and Vec::from_seq semantics.
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

    // build new sequence by mapping each element
    let new_seq: Seq<i32> = Seq::from_fn(old_len, |i: int| {
        if old_seq@[i] == x { y } else { old_seq@[i] }
    });

    // move new sequence into the vector
    *a = Vec::from_seq(new_seq);

    // final assertions to help verifier
    assert(a.len() == old_len);
    assert(a@ == new_seq);
    assert(forall |k: int| 0 <= k && k < (old_len as int) ==>
        a@[k] == if old_seq@[k] == x { y } else { old_seq@[k] });
}
// </vc-code>

fn main() {}
}