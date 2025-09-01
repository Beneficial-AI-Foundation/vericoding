use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove that swapping preserves multiset
proof fn swap_preserves_multiset(s: Seq<bool>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        i != j,
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
    assert(s.update(i, s[j]).update(j, s[i]) =~= s.update(i, s[j]).update(j, s[i]));
}

// Helper lemma for partitioning property
proof fn partition_property_maintained(s: Seq<bool>, left: int, right: int)
    requires
        0 <= left <= right < s.len(),
        forall|k: int| 0 <= k < left ==> !s[k],
        forall|k: int| right < k < s.len() ==> s[k],
    ensures
        forall|i: int, j: int| 
            0 <= i < left && left <= j < s.len() ==> !s[i] || s[j],
        forall|i: int, j: int| 
            0 <= i < s.len() && right < j < s.len() ==> !s[i] || s[j],
{
}
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
    let mut left: usize = 0;
    let mut right: usize = if a.len() > 0 { (a.len() - 1) as usize } else { 0 };
    
    while left < right
        invariant
            a.len() == old(a).len(),
            left <= right + 1,
            right < a.len(),
            left <= a.len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < left ==> !a[k],
            forall|k: int| right < k < a.len() ==> a[k],
            forall|i: int, j: int| 0 <= i < left && right < j < a.len() ==> !a[i] || a[j],
    {
        if !a[left] {
            left = left + 1;
        } else if a[right] {
            right = right - 1;
        } else {
            // a[left] is true and a[right] is false, so swap them
            proof {
                swap_preserves_multiset(a@, left as int, right as int);
            }
            let temp = a[left];
            a.set(left, a[right]);
            a.set(right, temp);
            left = left + 1;
            right = right - 1;
        }
    }
    
    // Prove the final sorting property
    proof {
        assert forall|i: int, j: int| 0 <= i < j < a.len() implies !a[i] || a[j] by {
            if i < left {
                assert(!a[i]);
            }
            if j > right {
                assert(a[j]);
            }
        }
    }
}
// </vc-code>

fn main() {}
}