use vstd::prelude::*;

verus! {

// Quicksort Partition -- Stephanie McIntyre
// Based on examples in class 
// Parts have been modified cause you know, arrays are different...

/* The annotations and implied proofs are left for you.
   I might do them later on next week. */

// <vc-helpers>
// Helper lemmas for reasoning about swaps and multisets

// Lemma: swapping two positions in a sequence yields a sequence whose multiset is equal to the original.
pub proof fn seq_swap_preserves(s: Seq<i32>, i: usize, j: usize)
    requires i < s.len() && j < s.len()
    ensures s.update(i, s@[j]).update(j, s@[i]).to_multiset() == s.to_multiset()
{
    proof {
        // Prove extensional equality of multisets by showing counts equal for every value.
        assert(forall|v: i32| #[trigger] s.update(i, s@[j]).update(j, s@[i]).to_multiset().count(v) == s.to_multiset().count(v));
    }
}

// Lemma: Vec::swap corresponds to two updates on the underlying sequence.
// This proof function performs the concrete swap and then relates the new sequence to the old sequence.
pub proof fn vec_swap_seq_update(x: &mut Vec<i32>, i: usize, j: usize)
    requires i < x.len() && j < x.len()
    ensures x@ == old(x)@.update(i, old(x)@[j]).update(j, old(x)@[i])
{
    proof {
        let before = old(x)@;
        // Perform the concrete swap on the vector (executable but inside a proof).
        x.swap(i, j);
        // After swap, the underlying sequence equals two updates of the old sequence.
        assert(x@ == before.update(i, before@[j]).update(j, before@[i]));
    }
}
// </vc-helpers>

// <vc-spec>
fn quicksort_partition(x: &mut Vec<i32>, n: usize, p: i32) -> (result: (usize, usize))
/*Pre-Condition*/   requires old(x).len() >= 1, n == old(x).len();
/*Post-Condition*/  ensures result.1 >= n;
                    ensures forall|i: int| 0 <= i < (result.0 as int) && (result.0 as int) < (n as int) ==> x[i] <= p;
                    ensures result.0 == n || (forall|i: int| (result.0 as int) <= i && i < (n as int) ==> x[i] > p);
                    ensures x@.to_multiset() == old(x)@.to_multiset()           //This says the new X is a permutation of our old version of X.
// </vc-spec>
// <vc-code>
{
    // Capture the original sequence as a ghost value to reason about multisets.
    let old_seq = x@;
    // n == old(x).len() is given by precondition.
    let mut store: usize = 0usize;
    let mut i: usize = 0usize;

    // Loop over all indices, maintaining invariants:
    //  - processed prefix [0, store) contains elements <= p
    //  - processed slice [store, i) contains elements > p
    //  - 0 <= store <= i <= n
    //  - multiset invariant: current x has same multiset as original
    while i < n
        invariant 0 <= store && store <= i && i <= n
        invariant forall |k: int| 0 <= k && (k as usize) < store ==> x[k as usize] <= p
        invariant forall |k: int| (store as int) <= k && (k as usize) < i ==> x[k as usize] > p
        invariant x@.to_multiset() == old_seq.to_multiset()
    {
        if x[i] <= p {
            // Save sequence before swap to apply lemmas
            let before = x@;
            // Perform the swap inside a proof-lemma to relate old and new sequences.
            proof {
                // This proof function performs the actual swap and yields the relation between x@ and before.
                vec_swap_seq_update(x, i, store);
                // The swapped sequence (computed from before) has the same multiset as before.
                seq_swap_preserves(before, i, store);
                // Combine facts: x@ equals the updated-before sequence, which has the same multiset as before.
                assert(x@.to_multiset() == before.to_multiset());
                // From the loop invariant before the swap, before.to_multiset() == old_seq.to_multiset().
                assert(before.to_multiset() == old_seq.to_multiset());
                // Hence x@ has same multiset as original old_seq.
                assert(x@.to_multiset() == old_seq.to_multiset());
                // Show that the element moved into 'store' is <= p:
                // x@[store] == before@[i] and before@[i] <= p (from the if-condition checked before).
                assert(x@[store] == before@[i]);
                assert(before@[i] <= p);
                assert(x@[store] <= p);
            }
            store = store + 1;
        }
        i = i + 1;
    }

    // Postconditions: return partition index and second component >= n
    (store, n)
}
// </vc-code>

fn main() {
}

}