use vstd::prelude::*;

verus! {

// Two-state predicate for checking if multiset is preserved
spec fn preserved(a_old: Seq<i32>, a_new: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a_old.len() && a_old.len() == a_new.len()
{
    a_old.subrange(left as int, right as int).to_multiset() == a_new.subrange(left as int, right as int).to_multiset()
}

// Predicate for checking if array slice is ordered
spec fn ordered(a: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a.len()
{
    forall|i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// Two-state predicate for sorted array
spec fn sorted(a_old: Seq<i32>, a_new: Seq<i32>) -> bool
    recommends a_old.len() == a_new.len()
{
    ordered(a_new, 0, a_new.len() as nat) && preserved(a_old, a_new, 0, a_old.len() as nat)
}

// <vc-helpers>
// Helper lemma: swapping preserves multiset
proof fn swap_preserves_multiset(a: Seq<i32>, i: nat, j: nat)
    requires 
        i < a.len(),
        j < a.len(),
    ensures 
        a.to_multiset() == a.update(i as int, a[j as int]).update(j as int, a[i as int]).to_multiset()
{
    // Verus can prove this automatically
}

// Helper lemma: swapping within a subrange preserves the multiset of that subrange
proof fn swap_preserves_subrange_multiset(a: Seq<i32>, i: nat, j: nat, left: nat, right: nat)
    requires 
        i < a.len(),
        j < a.len(),
        left <= i < right,
        left <= j < right,
        right <= a.len(),
    ensures 
        a.subrange(left as int, right as int).to_multiset() == 
        a.update(i as int, a[j as int]).update(j as int, a[i as int]).subrange(left as int, right as int).to_multiset()
{
    // Verus can prove this automatically
}

// Helper lemma: if we swap and maintain ordering properties
proof fn swap_maintains_ordering(a: Seq<i32>, i: nat, min_idx: nat)
    requires
        i < a.len(),
        min_idx < a.len(),
        i <= min_idx < a.len(),
        forall|k: int| #![trigger a[k]] i < k < a.len() ==> a[min_idx as int] <= a[k],
        ordered(a, 0, i as nat),
        i > 0 ==> a[(i - 1) as int] <= a[min_idx as int],
    ensures
        ordered(a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int]), 0, (i + 1) as nat)
{
    let a_new = a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int]);
    assert forall|k: int| #![trigger a_new[k]] 0 < k <= i implies a_new[k-1] <= a_new[k] by {
        if k == i as int {
            if i > 0 {
                assert(a_new[(i - 1) as int] == a[(i - 1) as int]);
                assert(a_new[i as int] == a[min_idx as int]);
                assert(a[(i - 1) as int] <= a[min_idx as int]);
            }
        } else {
            assert(a_new[k-1] == a[k-1]);
            assert(a_new[k] == a[k]);
            assert(a[k-1] <= a[k]);
        }
    }
}

// Helper lemma for maintaining the separation property after swap
proof fn swap_maintains_separation(a: Seq<i32>, i: nat, min_idx: nat)
    requires
        i < a.len(),
        min_idx < a.len(),
        i <= min_idx < a.len(),
        forall|k: int| #![trigger a[k]] i <= k < a.len() ==> a[min_idx as int] <= a[k],
        forall|k: int, m: int| #![trigger a[k], a[m]] 0 <= k < i && i <= m < a.len() ==> a[k] <= a[m],
    ensures
        forall|k: int, m: int| #![trigger a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int])[k], 
                                        a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int])[m]] 
            0 <= k <= i && i < m < a.len() ==> 
            a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int])[k] <= 
            a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int])[m]
{
    let a_new = a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int]);
    assert forall|k: int, m: int| #![trigger a_new[k], a_new[m]] 
        0 <= k <= i && i < m < a.len() implies a_new[k] <= a_new[m] by {
        if k == i as int {
            assert(a_new[k] == a[min_idx as int]);
            if m == min_idx as int {
                assert(a_new[m] == a[i as int]);
                assert(a[min_idx as int] <= a[i as int]);
            } else {
                assert(a_new[m] == a[m]);
                assert(a[min_idx as int] <= a[m]);
            }
        } else {
            assert(a_new[k] == a[k]);
            if m == min_idx as int {
                assert(a_new[m] == a[i as int]);
                assert(a[k] <= a[i as int]);
            } else {
                assert(a_new[m] == a[m]);
                assert(a[k] <= a[m]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(old(a)@, a@)
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n == 0 {
        return;
    }
    
    for i in 0..n
        invariant
            n == a.len(),
            ordered(a@, 0, i as nat),
            preserved(old(a)@, a@, 0, n as nat),
            forall|k: int, m: int| #![trigger a@[k], a@[m]] 0 <= k < i && i <= m < n ==> a@[k] <= a@[m],
    {
        let mut min_idx: usize = i;
        
        for j in (i + 1)..n
            invariant
                n == a.len(),
                i < n,
                min_idx < n,
                i <= min_idx < n,
                i < j <= n,
                ordered(a@, 0, i as nat),
                preserved(old(a)@, a@, 0, n as nat),
                forall|k: int, m: int| #![trigger a@[k], a@[m]] 0 <= k < i && i <= m < n ==> a@[k] <= a@[m],
                forall|k: int| #![trigger a@[k]] i <= k < j ==> a@[min_idx as int] <= a@[k],
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
        }
        
        if min_idx != i {
            let ghost old_a = a@;
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
            
            proof {
                assert(a@ == old_a.update(i as int, old_a[min_idx as int]).update(min_idx as int, old_a[i as int]));
                swap_preserves_multiset(old_a, i as nat, min_idx as nat);
                assert(preserved(old(a)@, a@, 0, n as nat));
                
                if i > 0 {
                    assert(old_a[(i - 1) as int] <= old_a[i as int]);
                    assert forall|m: int| #![trigger old_a[m]] i <= m < n implies old_a[(i - 1) as int] <= old_a[m] by {
                        assert(old_a[(i - 1) as int] <= old_a[m]);
                    }
                    assert(old_a[(i - 1) as int] <= old_a[min_idx as int]);
                }
                
                swap_maintains_ordering(old_a, i as nat, min_idx as nat);
                swap_maintains_separation(old_a, i as nat, min_idx as nat);
            }
        } else {
            proof {
                assert(ordered(a@, 0, (i + 1) as nat));
                assert forall|k: int, m: int| #![trigger a@[k], a@[m]] 
                    0 <= k <= i && i < m < n implies a@[k] <= a@[m] by {
                    if k == i as int {
                        assert(a@[k] == a@[i as int]);
                        assert forall|j: int| #![trigger a@[j]] i < j < n implies a@[i as int] <= a@[j] by {
                            assert(a@[min_idx as int] <= a@[j]);
                            assert(min_idx == i);
                        }
                    } else {
                        assert(a@[k] <= a@[m]);
                    }
                }
            }
        }
    }
    
    assert(ordered(a@, 0, n as nat));
    assert(preserved(old(a)@, a@, 0, n as nat));
}
// </vc-code>

fn main() {
}

}