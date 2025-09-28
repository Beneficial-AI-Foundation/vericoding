use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// <vc-helpers>
use vstd::multiset::*;
spec fn multiset_same_except_at_idx(s1: Seq<int>, s2: Seq<int>, i: int, j: int) -> bool {
    &&& s1.len() == s2.len()
    &&& (s1.to_multiset() - Multiset::singleton(s1[i]) - Multiset::singleton(s1[j])) =~= (s2.to_multiset() - Multiset::singleton(s2[i]) - Multiset::singleton(s2[j]))
}

proof fn lemma_multiset_swap<T>(s: Seq<T>, i: int, j: int, v1: T, v2: T)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        s[i] == v1,
        s[j] == v2,
    ensures
        s.update(i, v2).update(j, v1).to_multiset() =~= s.to_multiset(),
{
    assert(s.update(i, v2).update(j, v1).to_multiset() =~=
           (s.to_multiset() - Multiset::singleton(s[i]) - Multiset::singleton(s[j])) + Multiset::singleton(v2) + Multiset::singleton(v1));
    assert((s.to_multiset() - Multiset::singleton(s[i]) - Multiset::singleton(s[j])) + Multiset::singleton(s[j]) + Multiset::singleton(s[i]) =~= s.to_multiset()); // v1, v2 are s[i], s[j]
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
    let n = a.len(); // n is usize here, matched with a.len()

    proof {
        assert(a@.to_multiset() =~= a@.to_multiset()); // Trivially true, for verification.
    }

    let mut i: usize = 0;
    while (i as int) < (n as int)
        invariant
            a.len() == n,
            (n as int) >= 0,
            0 <= (i as int) <= (n as int),
            ordered(a@, 0, i as int),
            // Stronger outer loop invariant to ensure sorted part <= unsorted part
            forall |k1: int, k2: int| 0 <= k1 < (i as int) && (i as int) <= k2 < (n as int) ==> a@[k1] <= a@[k2],
            a@.to_multiset() =~= old(a)@.to_multiset(),
    {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;

        proof {
            assert(ordered(a@, 0, i as int)); // from outer loop invariant
            assert(a@.to_multiset() =~= old(a)@.to_multiset()); // from outer loop invariant
        }

        while (j as int) < (n as int)
            invariant
                a.len() == n,
                (n as int) >= 0,
                0 <= (i as int) < (n as int),
                0 <= (j as int) <= (n as int),
                (i as int) <= (min_idx as int) < (j as int),
                forall |k: int| (i as int) <= k < (j as int) ==> a@[min_idx as int] <= a@[k],
                a@.to_multiset() =~= old(a)@.to_multiset(),
            decreases (n - j) as int
        {
            if a@[j as int] < a@[min_idx as int] {
                min_idx = j;
            }
            j = j + 1;
        }

        if i != min_idx {
            let old_a_seq = a@;
            let old_a_at_i = a@[i as int];
            let old_a_at_min_idx = a@[min_idx as int];

            a.swap(i, min_idx);

            proof {
                assert(a.len() == n);
                lemma_multiset_swap(old_a_seq, i as int, min_idx as int, old_a_at_i, old_a_at_min_idx);
                assert(a@.to_multiset() =~= old_a_seq.to_multiset());
                assert(a@.to_multiset() =~= old(a)@.to_multiset());
            }
        }

        proof {
            // Prove that a[i] is the smallest element from a[i] to a[n-1]
            // This is guaranteed by the inner loop invariant: forall |k: int| i <= k < j ==> a@[min_idx] <= a@[k]
            // After the inner loop, j == n, so forall |k: int| i <= k < n ==> a@[min_idx] <= a@[k]
            // And if i != min_idx, a[i] becomes the value that was at a[min_idx].
            assert(forall |k: int| (i as int) <= k < (n as int) ==> a@[i as int] <= a@[k]);


            // Prove ordered property for the current i+1
            if (i as int) > 0 {
                // Assert from outer loop invariant
                assert(ordered(a@, 0, i as int));

                // We need to show that a@[i-1] <= a@[i] after the swap.
                // The element at a@[i] position (after swap) is the minimum of original `a@.subsequence(i, n)`.
                // From the stronger outer loop invariant:
                // forall |k1: int, k2: int| 0 <= k1 < i && i <= k2 < n ==> old(a)@[k1] <= old(a)@[k2]
                // We apply this with k1 = i-1 and k2 = min_idx (before swap, from old(a)@).
                // So, old(a)@[i-1] <= old(a)@[min_idx].
                // After the swap, a@[i-1] is old(a)@[i-1] (unchanged for k < i).
                // And a@[i] is old(a)@[min_idx].
                // Therefore, a@[i-1] <= a@[i].
                let pre_a_val = old(a)@;
                assert(pre_a_val@[(i - 1) as int] <= pre_a_val@[min_idx as int]); // From outer loop invariant applied to pre-state
                assert(a@[(i - 1) as int] == pre_a_val@[(i - 1) as int]); // Unchanged prefix
                assert(a@[i as int] == pre_a_val@[min_idx as int]); // The element at i is now the minimum from the unsorted part
                assert(a@[(i - 1) as int] <= a@[i as int]);
                assert(ordered(a@, 0, (i + 1) as int));
            } else { // i == 0
                assert(ordered(a@, 0, 1));
            }

            // Update the stronger outer loop invariant
            assert forall |k1: int, k2: int| 0 <= k1 < (i+1) as int && (i+1) as int <= k2 < (n as int) implies a@[k1] <= a@[k2] by {
                let pre_a = old(a)@; // The value of a@ at the beginning of the outer loop iteration
                
                if k1 < (i as int) { // k1 is in the already sorted prefix before current i
                    assert(a@[k1] == pre_a@[k1]); // a@[k1] is unchanged
                    // a@[i] is now the smallest element from pre_a.subsequence(i,n)
                    // From outer loop invariant for pre_a: pre_a@[k1] <= pre_a@[i] and pre_a@[k1] <= pre_a@[min_idx]
                    // Since a@[i] is pre_a@[min_idx], we have a@[k1] <= a@[i].
                    // Any element a@[k2] for k2 >= i+1, is some element from pre_a.subsequence(i,n),
                    // which means pre_a@[min_idx] <= a@[k2].
                    // So a@[k1] <= a@[i] <= a@[k2].
                    assert(pre_a@[k1] <= pre_a@[min_idx as int]); // from outer loop invariant at the start of original loop for initial pre_a (k1 < i, and min_idx is >= i)
                    assert(a@[k1] == pre_a@[k1]);
                    assert(a@[k2] >= a@[i as int]); // a@[k2] is an element from the 'unsorted' suffix, and a@[i] is the minimum of that suffix
                    assert(a@[i as int] == pre_a@[min_idx as int]);
                    assert(a@[k1] <= a@[i as int]); // already proved
                    assert(a@[k1] <= a@[k2]);
                } else { // k1 == i
                    // We need to show a@[i] <= a@[k2] for k2 >= i+1.
                    // This is directly implied by the fact that a@[i] is the minimum element in a.subsequence(i,n).
                    assert(a@[i as int] <= a@[k2]);
                }
            }
        }
        i = i + 1;
    }

    proof {
        assert(ordered(a@, 0, n as int));
        assert(a.len() == n);
    }
}
// </vc-code>

fn main() {}

}