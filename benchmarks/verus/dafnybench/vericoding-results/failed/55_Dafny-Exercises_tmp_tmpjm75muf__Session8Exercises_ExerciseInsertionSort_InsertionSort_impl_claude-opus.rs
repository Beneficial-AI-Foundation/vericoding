use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
// Helper lemma to show that swapping preserves multiset
proof fn swap_preserves_multiset(a: Seq<i32>, i: int, j: int)
    requires 
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures 
        a.update(i, a[j]).update(j, a[i]).to_multiset() == a.to_multiset()
{
    // Verus can prove this automatically
}

// Helper to show that updating preserves sorted segments outside the update region
proof fn update_preserves_sorted_seg(a: &Vec<i32>, old_a: &Vec<i32>, i: int, j: int, update_idx: int)
    requires
        0 <= i <= j + 1 <= a.len(),
        0 <= i <= j + 1 <= old_a.len(),
        a.len() == old_a.len(),
        0 <= update_idx < a.len(),
        sorted_seg(old_a, i, j),
        forall|k: int| 0 <= k < a.len() && k != update_idx ==> a[k] == old_a[k],
        (update_idx < i || update_idx > j),
    ensures
        sorted_seg(a, i, j)
{
    assert forall|l: int, k: int| i <= l <= k <= j implies a[l] <= a[k] by {
        assert(a[l] == old_a[l]);
        assert(a[k] == old_a[k]);
    }
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    ensures 
        sorted_seg(a, 0, (a.len() - 1) as int),
        a@.to_multiset() == old(a)@.to_multiset(), //Add and prove this
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n == 0 {
        return;
    }
    
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            n == a.len(),
            sorted_seg(a, 0, (i - 1) as int),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let ghost old_a_at_i_start = a@;
        let key = a[i];
        let mut j: usize = i;
        
        while j > 0 && a[j - 1] > key
            invariant
                0 <= j <= i < n,
                n == a.len(),
                key == old_a_at_i_start[i as int],
                sorted_seg(a, 0, (j - 1) as int),
                sorted_seg(a, j as int, i as int),
                forall|k: int| j as int < k <= i as int ==> #[trigger] a[k] >= key,
                forall|k: int| 0 <= k < j as int ==> #[trigger] a[k] <= a[(j - 1) as int],
                a@.to_multiset() == old(a)@.to_multiset(),
                forall|k: int| j as int < k <= i as int ==> a[k] == old_a_at_i_start[(k - 1) as int],
                j < i ==> a[i as int] == old_a_at_i_start[(i - 1) as int],
        {
            let val = a[j - 1];  // Store value first to avoid borrowing issue
            a.set(j, val);
            j = j - 1;
        }
        
        a.set(j, key);
        
        // Prove that after inserting key at position j, segment [0, i] is sorted
        assert forall|l: int, k: int| 0 <= l <= k <= i as int implies a[l] <= a[k] by {
            if l < j as int && k < j as int {
                // Both in left sorted part [0, j-1]
                assert(sorted_seg(a, 0, (j - 1) as int));
            } else if l == j as int && k == j as int {
                // Same position (key)
                assert(a[l] == key && a[k] == key);
            } else if l < j as int && k == j as int {
                // l in left part, k at key position
                assert(a[l] <= a[(j - 1) as int]);
                assert(a[(j - 1) as int] <= key);
            } else if l == j as int && k > j as int && k <= i as int {
                // l at key position, k in right part
                assert(key <= a[k]);
            } else if l < j as int && k > j as int && k <= i as int {
                // l in left part, k in right part
                assert(a[l] <= a[(j - 1) as int]);
                assert(a[(j - 1) as int] <= key);
                assert(key <= a[k]);
            } else if l > j as int && k > j as int && k <= i as int {
                // Both in right sorted part
                assert(sorted_seg(a, j as int, i as int));
            }
        }
        
        i = i + 1;
    }
    
    assert(i == n);
    assert(sorted_seg(a, 0, (n - 1) as int));
}
// </vc-code>

fn main() {}

}