use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    // pre-conditions-start
    requires
        old(a).len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n = a.len();
    let old_ms = a@.to_multiset();
    let mut l: int = 0;
    let mut r: int = (n as int) - 1;
    while l < r
        invariant { 0 <= l && l <= n as int; }
        invariant { -1 <= r && r < n as int; }
        invariant { l <= r + 1; }
        invariant { forall|i: int| 0 <= i < l ==> !a@[i]; }
        invariant { forall|i: int| r < i && i < n as int ==> a@[i]; }
        invariant { a@.to_multiset() == old_ms; }
    {
        if !a@[l] {
            l += 1;
        } else if a@[r] {
            r -= 1;
        } else {
            a.swap(l as usize, r as usize);
            l += 1;
            r -= 1;
        }
    }

    // final proofs: length preserved, multiset preserved (invariant), and ordering holds
    proof {
        assert(a.len() == n);
        assert(a@.to_multiset() == old_ms);
        assert(!(l < r));
        assert(l >= r);

        assert(forall|i: int, j: int| 0 <= i < j && j < n as int ==>
            (
                if i < l {
                    // then by invariant positions < l are false
                    assert(0 <= i && i < l);
                    assert(!a@[i]);
                    !a@[i] || a@[j]
                } else {
                    // i >= l. From i < j and l >= r we get j > r, so position j is true.
                    assert(!(i < l));
                    assert(i >= l);
                    assert(l >= r);
                    assert(i >= r);
                    assert(j > r);
                    assert(a@[j]);
                    !a@[i] || a@[j]
                }
            )
        );

        assert(forall|i: int, j: int| 0 <= i < j && j < n as int ==> !a@[i] || a@[j]);
    }

    ()
    // impl-end
}
// </vc-code>

fn main() {}
}