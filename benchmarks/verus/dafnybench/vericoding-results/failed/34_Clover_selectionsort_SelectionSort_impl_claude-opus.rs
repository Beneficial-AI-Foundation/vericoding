use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma: swapping two elements preserves the multiset
proof fn swap_preserves_multiset(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset()
{
    assert(s.update(i, s[j]).update(j, s[i]) =~= s.update(i, s[j]).update(j, s[i]));
}

// Helper lemma: if we update an element at position >= n, the prefix before n remains unchanged
proof fn update_preserves_prefix(s: Seq<i32>, n: int, idx: int, val: i32)
    requires
        0 <= n <= s.len(),
        n <= idx < s.len(),
    ensures
        forall|k: int| 0 <= k < n ==> s.update(idx, val)[k] == s[k]
{
}

// Helper lemma: sorted prefix remains sorted after updating elements beyond it
proof fn sorted_prefix_preserved(s: Seq<i32>, n: int, i: int, j: int)
    requires
        0 <= n <= s.len(),
        n <= i < s.len(),
        n <= j < s.len(),
        forall|a: int, b: int| 0 <= a < b < n ==> s[a] <= s[b],
    ensures
        forall|a: int, b: int| 0 <= a < b < n ==> s.update(i, s[j]).update(j, s[i])[a] <= s.update(i, s[j]).update(j, s[i])[b]
{
    assert forall|a: int, b: int| 0 <= a < b < n implies s.update(i, s[j]).update(j, s[i])[a] <= s.update(i, s[j]).update(j, s[i])[b] by {
        update_preserves_prefix(s, n, i, s[j]);
        update_preserves_prefix(s.update(i, s[j]), n, j, s[i]);
    }
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    
    for i in 0..n
        invariant
            a.len() == n,
            // The first i elements are sorted
            forall|j: int, k: int| 0 <= j < k < i as int ==> a[j] <= a[k],
            // Every element in the sorted portion is <= every element in the unsorted portion
            forall|j: int, k: int| 0 <= j < i as int && i as int <= k < n as int ==> a[j] <= a[k],
            // Multiset is preserved
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        // Find the minimum element in a[i..n]
        let mut min_idx: usize = i;
        
        for j in (i + 1)..n
            invariant
                a.len() == n,
                i <= min_idx < j,
                j <= n + 1,
                // min_idx points to the minimum element seen so far in a[i..j)
                forall|k: int| i as int <= k < j as int ==> a[min_idx as int] <= a[k],
                // Maintain outer loop invariants
                forall|j: int, k: int| 0 <= j < k < i as int ==> a[j] <= a[k],
                forall|j: int, k: int| 0 <= j < i as int && i as int <= k < n as int ==> a[j] <= a[k],
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
        }
        
        // Swap a[i] with a[min_idx]
        if i != min_idx {
            let old_a = a@;
            let temp = a[i];
            a.set(i, a[min_idx]);
            
            proof {
                assert(a@ == old_a.update(i as int, old_a[min_idx as int]));
            }
            
            a.set(min_idx, temp);
            
            proof {
                assert(a@ == old_a.update(i as int, old_a[min_idx as int]).update(min_idx as int, temp));
                assert(temp == old_a[i as int]);
                swap_preserves_multiset(old_a, i as int, min_idx as int);
                assert(a@.to_multiset() == old_a.to_multiset());
                
                // Prove that sorted prefix is preserved
                sorted_prefix_preserved(old_a, i as int, i as int, min_idx as int);
                
                // Prove the new element at position i maintains the invariants
                assert forall|j: int, k: int| 0 <= j < k <= i as int implies a[j] <= a[k] by {
                    if k < i as int {
                        assert(a[j] == old_a[j]);
                        assert(a[k] == old_a[k]);
                    } else {
                        assert(k == i as int);
                        if j < i as int {
                            assert(a[j] == old_a[j]);
                            assert(a[j] <= old_a[i as int]);
                            assert(a[i as int] == old_a[min_idx as int]);
                            assert(old_a[min_idx as int] <= old_a[k] || k == min_idx as int);
                        }
                    }
                }
                
                // Prove separation between sorted and unsorted portions
                assert forall|j: int, k: int| (0 <= j <= i as int && i as int < k < n as int) implies a[j] <= a[k] by {
                    if j < i as int {
                        assert(a[j] == old_a[j]);
                        assert(old_a[j] <= old_a[k]);
                        assert(a[k] == old_a[k] || k == min_idx as int);
                        if k == min_idx as int {
                            assert(a[k] == old_a[i as int]);
                            assert(old_a[j] <= old_a[i as int]);
                        }
                    } else {
                        assert(j == i as int);
                        assert(a[i as int] == old_a[min_idx as int]);
                        assert(old_a[min_idx as int] <= old_a[k] || k == min_idx as int);
                        if k == min_idx as int {
                            assert(a[k] == old_a[i as int]);
                        } else {
                            assert(a[k] == old_a[k]);
                        }
                    }
                }
            }
        }
    }
}
// </vc-code>

fn main() {}

}