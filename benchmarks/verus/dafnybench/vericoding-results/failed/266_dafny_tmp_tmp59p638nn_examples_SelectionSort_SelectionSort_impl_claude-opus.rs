use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// <vc-helpers>
// Helper lemma to show that swapping preserves multiset
proof fn swap_preserves_multiset(a: Seq<int>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a.update(i, a[j]).update(j, a[i]).to_multiset() =~= a.to_multiset()
{
    let swapped = a.update(i, a[j]).update(j, a[i]);
    assert forall |k: int| 0 <= k < a.len() implies 
        #[trigger] swapped.to_multiset().count(a[k]) == a.to_multiset().count(a[k]) by {
        if k == i {
            assert(swapped[i] == a[j]);
        } else if k == j {
            assert(swapped[j] == a[i]);
        } else {
            assert(swapped[k] == a[k]);
        }
    }
}

// Helper lemma for ordered property after placing minimum at position
proof fn ordered_after_min_placement(a: Seq<int>, i: int, min_idx: int)
    requires
        0 <= i < a.len(),
        i <= min_idx < a.len(),
        ordered(a, 0, i),
        forall |k: int| i <= k < a.len() ==> a[min_idx] <= a[k],
        forall |j: int, k: int| 0 <= j < i <= k < a.len() ==> a[j] <= a[k],
    ensures
        ordered(a.update(i, a[min_idx]).update(min_idx, a[i]), 0, i + 1)
{
    let swapped = a.update(i, a[min_idx]).update(min_idx, a[i]);
    assert forall |k: int| 0 < k <= i + 1 implies #[trigger] swapped[k-1] <= swapped[k] by {
        if k < i {
            assert(swapped[k-1] == a[k-1]);
            assert(swapped[k] == a[k]);
            assert(a[k-1] <= a[k]);
        } else if k == i {
            assert(swapped[k-1] == a[k-1]);
            assert(swapped[k] == a[min_idx]);
            assert(a[k-1] <= a[min_idx]);
        } else if k == i + 1 {
            assert(swapped[i] == a[min_idx]);
            assert(a[min_idx] <= a[i]);
        }
    }
}

// Helper lemma to maintain cross-partition ordering
proof fn maintain_cross_partition_ordering(a: Seq<int>, i: int, min_idx: int)
    requires
        0 <= i < a.len(),
        i <= min_idx < a.len(),
        forall |j: int, k: int| 0 <= j < i <= k < a.len() ==> a[j] <= a[k],
        forall |k: int| i <= k < a.len() ==> a[min_idx] <= a[k],
    ensures
        forall |j: int, k: int| 0 <= j < i + 1 <= k < a.len() ==> 
            a.update(i, a[min_idx]).update(min_idx, a[i])[j] <= a.update(i, a[min_idx]).update(min_idx, a[i])[k]
{
    let swapped = a.update(i, a[min_idx]).update(min_idx, a[i]);
    assert forall |j: int, k: int| 0 <= j < i + 1 <= k < a.len() implies 
        #[trigger] swapped[j] <= #[trigger] swapped[k] by {
        if j < i {
            assert(swapped[j] == a[j]);
            if k == min_idx {
                assert(swapped[k] == a[i]);
                assert(a[j] <= a[i]);
            } else {
                assert(swapped[k] == a[k]);
                assert(a[j] <= a[k]);
            }
        } else if j == i {
            assert(swapped[j] == a[min_idx]);
            if k == min_idx {
                assert(swapped[k] == a[i]);
                assert(a[min_idx] <= a[i]);
            } else {
                assert(swapped[k] == a[k]);
                assert(a[min_idx] <= a[k]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures 
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    
    for i in 0..n
        invariant
            a.len() == n,
            ordered(a@, 0, i as int),
            a@.to_multiset() =~= old(a)@.to_multiset(),
            forall |j: int, k: int| 0 <= j < i <= k < n ==> a@[j] <= a@[k],
    {
        let mut min_idx = i;
        
        for j in (i + 1)..n
            invariant
                a.len() == n,
                i <= min_idx < n,
                forall |k: int| i <= k < j ==> a@[min_idx as int] <= a@[k],
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
        }
        
        if min_idx != i {
            let ghost old_a = a@;
            let temp = a[i];
            let min_val = a[min_idx];
            a.set(i, min_val);
            a.set(min_idx, temp);
            
            proof {
                swap_preserves_multiset(old_a, i as int, min_idx as int);
                assert(a@ =~= old_a.update(i as int, old_a[min_idx as int]).update(min_idx as int, old_a[i as int]));
                ordered_after_min_placement(old_a, i as int, min_idx as int);
                maintain_cross_partition_ordering(old_a, i as int, min_idx as int);
            }
        }
    }
}
// </vc-code>

fn main() {}

}