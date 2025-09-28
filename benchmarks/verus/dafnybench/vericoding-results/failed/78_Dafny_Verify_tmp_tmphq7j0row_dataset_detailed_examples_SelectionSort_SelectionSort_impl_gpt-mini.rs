use vstd::prelude::*;

verus! {

// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
proof fn seq_swap_preserves_multiset(s: Seq<i32>, i: nat, j: nat)
    ensures s.update(i, s@[j]).update(j, s@[i]).to_multiset() == s.to_multiset()
{
    if i == j {
        // No-op swap
        assert(s.update(i, s@[j]).update(j, s@[i]) == s);
        return;
    }

    // We show equality of multisets by showing equality of counts for every value.
    // For any value v, the count in the updated sequence equals the count in the original.
    forall|v: i32| {
        // Count in original
        let orig_count = s.to_multiset().count(v);

        // After first update: replace s[i] with s[j]
        let after1 = s.update(i, s@[j]);
        // after1 multiset = orig - {s@[i]} + {s@[j]}
        // After second update: replace position j (which currently holds s@[j]) with original s@[i]
        let after2 = after1.update(j, s@[i]);
        // after2 multiset = after1 - {s@[j]} + {s@[i]} = orig

        // Now compute counts stepwise
        let c_orig = orig_count;
        // count after1: decrement if s@[i]==v, increment if s@[j]==v
        let c_after1 =
            c_orig
            - if s@[i] == v { 1 } else { 0 }
            + if s@[j] == v { 1 } else { 0 };

        // count after2: decrement if after1@[j]==v (which is s@[j]==v), increment if s@[i]==v
        let c_after2 =
            c_after1
            - if s@[j] == v { 1 } else { 0 }
            + if s@[i] == v { 1 } else { 0 };

        assert(c_after2 == c_orig) by {
            // algebraic cancellations:
            // c_after2 = c_orig - (s@[i]==v ? 1 : 0) + (s@[j]==v ? 1 : 0) - (s@[j]==v ? 1 : 0) + (s@[i]==v ? 1 : 0)
            //         = c_orig
        };

        // thus counts equal for arbitrary v
        assert(after2.to_multiset().count(v) == orig_count);
    };

    // Having shown counts equal for all v, multisets are equal.
    // Use multiset extensionality (provided by the library).
    assert(s.update(i, s@[j]).update(j, s@[i]).to_multiset() == s.to_multiset());
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        // Ensures the final array is sorted in ascending order
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        // Ensures that the final array has the same elements as the initial array
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    // In-place selection sort with loop invariants proving sortedness and multiset preservation
    let n = a.len();

    // Save the original multiset to relate to at the end
    let old_ms = a@.to_multiset();

    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant forall|p: int, q: int| 0 <= p && p < q && q < (i as int) ==> a@[(p as nat)] <= a@[(q as nat)]
        invariant forall|p: int, t: int| 0 <= p && p < (i as int) && (i as int) <= t && t < (n as int) ==> a@[(p as nat)] <= a@[(t as nat)]
        invariant a@.to_multiset() == old_ms
    {
        // Find index of minimum element in [i, n)
        let mut mi: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant i <= mi && mi < n
            invariant i <= j && j <= n
            invariant forall|t: int| (i as int) <= t && t < (j as int) ==> a@[(mi as nat)] <= a@[(t as nat)]
            invariant a@.to_multiset() == old_ms
        {
            if a@[j] < a@[mi] {
                mi = j;
            }
            j += 1;
        }

        // Capture sequence before swap to apply multiset lemma
        if mi != i {
            let seq_before = a@;
            a.swap(i, mi);
            // After swap, the concrete sequence equals seq_before with the two entries swapped.
            // From that, use seq_swap_preserves_multiset to show the multiset is unchanged.
            assert(a@ == seq_before.update(i, seq_before@[mi]).update(mi, seq_before@[i]));
            seq_swap_preserves_multiset(seq_before, i, mi);
            assert(a@.to_multiset() == seq_before.to_multiset());
            // By the loop invariant before swap, seq_before.to_multiset() == old_ms, so preserved.
        }

        i += 1;
    }

    // At loop exit i == n, use invariants to conclude full sortedness
    proof {
        // From invariant, for all p<q<i (here i==n), a[p] <= a[q]
        assert(forall|p: int, q: int| 0 <= p && p < q && q < (n as int) ==> a@[(p as nat)] <= a@[(q as nat)]);
        // And multiset equality is maintained as required
        assert(a@.to_multiset() == old_ms);
    }
}
// </vc-code>

fn main() {
}

}