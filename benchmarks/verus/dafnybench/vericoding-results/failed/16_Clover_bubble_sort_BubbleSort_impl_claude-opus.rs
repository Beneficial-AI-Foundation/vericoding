use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper predicate to check if a sequence is sorted
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Helper lemma: swapping adjacent elements preserves multiset
proof fn swap_preserves_multiset(s: Seq<i32>, i: int)
    requires
        0 <= i,
        i + 1 < s.len(),
    ensures
        s.update(i, s[i + 1]).update(i + 1, s[i]).to_multiset() == s.to_multiset(),
{
    let s_swapped = s.update(i, s[i + 1]).update(i + 1, s[i]);
    assert(s_swapped.len() == s.len());
    
    // Prove multiset equality by showing each element appears the same number of times
    assert forall|v: i32| #[trigger] s.to_multiset().count(v) == s_swapped.to_multiset().count(v) by {
        // Elements at positions i and i+1 are swapped
        if v == s[i] && v == s[i + 1] {
            // Both positions have the same value, no change in count
        } else if v == s[i] {
            // v appears at position i+1 in swapped version
            assert(s_swapped[i + 1] == v);
        } else if v == s[i + 1] {
            // v appears at position i in swapped version  
            assert(s_swapped[i] == v);
        }
        // All other positions unchanged
        assert forall|k: int| 0 <= k < s.len() && k != i && k != i + 1 ==> s_swapped[k] == s[k];
    }
    assert(s_swapped.to_multiset() =~= s.to_multiset());
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n == 0 {
        return;
    }
    
    for i in 0..n
        invariant
            forall|k: int, l: int| (n - i) <= k < l < n ==> #[trigger] a@[k] <= #[trigger] a@[l],
            forall|k: int| 0 <= k < (n - i) ==> 
                forall|l: int| (n - i) <= l < n ==> #[trigger] a@[k] <= #[trigger] a@[l],
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        if i >= n - 1 {
            continue;
        }
        
        for j in 0..(n - i - 1)
            invariant
                j <= n - i - 1,
                forall|k: int, l: int| (n - i) <= k < l < n ==> #[trigger] a@[k] <= #[trigger] a@[l],
                forall|k: int| 0 <= k < (n - i) ==> 
                    forall|l: int| (n - i) <= l < n ==> #[trigger] a@[k] <= #[trigger] a@[l],
                forall|k: int| 0 <= k < j ==> #[trigger] a@[k] <= #[trigger] a@[j as int],
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            assert(j < n - i - 1);
            assert(j + 1 < n);
            
            if a[j] > a[j + 1] {
                proof {
                    swap_preserves_multiset(a@, j as int);
                }
                let val_j = a[j];
                let val_j_plus_1 = a[j + 1];
                a.set(j, val_j_plus_1);
                a.set(j + 1, val_j);
                
                assert(a@[j as int] == val_j_plus_1);
                assert(a@[(j + 1) as int] == val_j);
            }
        }
        
        // After inner loop, element at position n - i - 1 is in its final position
        assert(forall|k: int| 0 <= k < n - i - 1 ==> a@[k] <= a@[n - i - 1]);
    }
    
    // Prove the final postcondition
    assert forall|i: int, j: int| 0 <= i < j < a.len() implies a@[i] <= a@[j] by {
        assert(n - n == 0);
        // All elements are sorted because (n - n) = 0
    }
}
// </vc-code>

fn main() {
}

}