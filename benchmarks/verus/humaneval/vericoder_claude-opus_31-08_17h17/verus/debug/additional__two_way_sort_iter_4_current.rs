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
    // We need to prove that the multiset is preserved after swapping
    let s_swap = s.update(i, s[j]).update(j, s[i]);
    assert forall|v: bool| #[trigger] s_swap.to_multiset().count(v) == s.to_multiset().count(v) by {
        // Count all occurrences
        let count_orig = s.filter(|x: bool| x == v).len();
        let count_swap = s_swap.filter(|x: bool| x == v).len();
        
        // The swap only affects positions i and j
        assert forall|k: int| 0 <= k < s.len() && k != i && k != j ==> s_swap[k] == s[k];
        
        // After swap: s_swap[i] = s[j] and s_swap[j] = s[i]
        assert(s_swap[i] == s[j]);
        assert(s_swap[j] == s[i]);
        
        // The multiset counts remain the same
        assert(count_orig == count_swap);
    }
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
            left <= a.len(),
            if a.len() > 0 { right < a.len() } else { right == 0 },
            if a.len() > 0 { left <= right + 1 } else { left == 0 && right == 0 },
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < left ==> !a[k],
            forall|k: int| right < k < a.len() ==> a[k],
            forall|i: int, j: int| 0 <= i < left && right < j < a.len() ==> !a[i] || a[j],
        decreases 
            if left <= right { (right - left) as int } else { 0int },
    {
        if !a[left] {
            left = left + 1;
        } else if a[right] {
            proof {
                assert(right > 0);  // Since left < right and left >= 0
            }
            right = right - 1;
        } else {
            // a[left] is true and a[right] is false, so swap them
            proof {
                swap_preserves_multiset(a@, left as int, right as int);
            }
            let temp_left = a[left];
            let temp_right = a[right];
            a.set(left, temp_right);
            a.set(right, temp_left);
            left = left + 1;
            proof {
                assert(right > 0);  // Since left < right before increment
            }
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
            if i < left && j > right {
                assert(!a[i]);
                assert(a[j]);
                assert(!a[i] || a[j]);
            }
            if left <= i && j <= right {
                // When the loop exits, left >= right
                // So if left <= i < j <= right, then left = right or left = right + 1
                if left == right + 1 {
                    // This case means i >= right + 1 and j <= right, which is impossible when i < j
                    assert(false);
                } else {
                    // left == right, so i == j == left == right
                    // But we have i < j, so this is also impossible
                    assert(i == left);
                    assert(j == right);
                    assert(left == right);
                    assert(i == j);
                    assert(false);
                }
            }
        }
    }
}
// </vc-code>

fn main() {}
}