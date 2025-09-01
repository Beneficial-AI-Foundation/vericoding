use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn replace_lemma(s: Seq<i32>, s_new: Seq<i32>, x: i32, y: i32, k: int)
    requires
        0 <= k < s.len(),
        s_new.len() == s.len(),
        forall|i: int| 0 <= i < s.len() && s[i] == x ==> s_new[i] == y,
        forall|i: int| 0 <= i < s.len() && s[i] != x ==> s_new[i] == s[i],
    ensures
        s[k] == x ==> s_new[k] == y,
        s[k] != x ==> s_new[k] == s[k],
{
}

proof fn vec_ext_eq<A>(v1: Vec<A>, v2: Vec<A>)
    requires
        v1@ =~= v2@,
    ensures
        v1 == v2,
{
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
    let old_a = a@;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == old_a.len(),
            forall|k: int| 0 <= k < i && old_a[k] == x ==> a@[k] == y,
            forall|k: int| 0 <= k < i && old_a[k] != x ==> a@[k] == old_a[k],
            forall|k: int| i <= k < old_a.len() ==> a@[k] == old_a[k],
    {
        let elem = a[i];
        if elem == x {
            a[i] = y;
            proof {
                assert forall|k: int| 0 <= k < i+1 && old_a[k] == x implies a@[k] == y by {
                    if k == i as int {
                        assert(old_a[k] == x ==> a@[k] == y);
                    } else {
                        assert(0 <= k < i);
                    }
                };
                assert forall|k: int| 0 <= k < i+1 && old_a[k] != x implies a@[k] == old_a[k] by {
                    if k == i as int {
                        assert(old_a[k] != x ==> a@[k] == old_a[k]);
                    } else {
                        assert(0 <= k < i);
                    }
                };
                assert forall|k: int| i+1 <= k < old_a.len() implies a@[k] == old_a[k] by {
                    assert(i <= k < old_a.len());
                };
            }
        } else {
            proof {
                assert forall|k: int| 0 <= k < i+1 && old_a[k] == x implies a@[k] == y by {
                    if k == i as int {
                        assert(old_a[k] != x);
                    }
                };
                assert forall|k: int| 0 <= k < i+1 && old_a[k] != x implies a@[k] == old_a[k] by {
                    if k == i as int {
                        assert(a@[k] == old_a[k]);
                    }
                };
                assert forall|k: int| i+1 <= k < old_a.len() implies a@[k] == old_a[k] by {
                    assert(i <= k < old_a.len());
                };
            }
        }
        i = i + 1;
    }
    proof {
        assert(a@.len() == old_a.len());
        assert forall|k: int| 0 <= k < old_a.len() && old_a[k] == x implies a@[k] == y by {
            assert(0 <= k < a@.len());
            replace_lemma(old_a, a@, x, y, k);
        };
        assert forall|k: int| 0 <= k < old_a.len() && old_a[k] != x implies a@[k] == old_a[k] by {
            assert(0 <= k < a@.len());
            replace_lemma(old_a, a@, x, y, k);
        };
        vec_ext_eq(*old(a), *a);
    }
}
// </vc-code>

fn main() {}
}