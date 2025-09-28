use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
proof fn lemma_forall_equal_transitive<T>(s: Seq<Seq<T>>, f: spec_fn(int, int) -> bool)
    requires
        s.len() >= 0,
        forall |i: int, j: int|
            #[trigger] f(i, j) == (s.index(i).len() == s.index(j).len()),
        forall |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> f(i,j),
    ensures
        forall |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s.index(i).len() == s.index(j).len()
{
    // This lemma is a placeholder for the natural transitivity of equality.
    // Verus usually handles this directly but sometimes needs a hint.
    // For this specific problem, the direct proof for the loop invariant is sufficient.
}

proof fn current_seq_len_pos<T>(sequences: Seq<Seq<T>>, i: int)
    requires
        0 <= i < sequences.len(),
    ensures
        sequences.len() >= 0, // This is always true for Seq, but adding it for clarity.
{
    // This is essentially re-asserting the precondition for internal verification.
}
// </vc-helpers>

// <vc-spec>
fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
// </vc-spec>
// <vc-code>
{
    if sequences.len() <= 1 {
        // If there are 0 or 1 sequences, the condition is vacuously true.
        assert(forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences.index(i).len() == sequences.index(j).len());
        return true;
    }

    let first_len: nat = sequences.index(0).len();
    let mut i: nat = 1;

    // Invariant: For all k from 0 to i-1, sequences[k].len() == first_len
    // And for all p, q such that 0 <= p < i and 0 <= q < i, sequences[p].len() == sequences[q].len()
    // This second part of the invariant is crucial for the post-condition.
    // It's derived from the first part and transitivity of equality.
    while i < sequences.len()
        invariant
            1 <= i <= sequences.len(),
            sequences.len() > 0, // Must hold if we entered the loop
            sequences.index(0).len() == first_len, // Initial state for sequences[0]
            forall |k: int| 0 <= k < i ==> sequences.index(k).len() == first_len,
            // Prove the necessary condition for items processed so far:
            forall |p: int, q: int| 0 <= p < i && 0 <= q < i ==> sequences.index(p).len() == sequences.index(q).len(),
    {
        proof {
            current_seq_len_pos(sequences, i as int); // Assert point_to(i)
        }
        if sequences.index(i as int).len() != first_len {
            return false;
        }

        // Asserting the loop invariant for the next iteration step (i+1)
        assert(sequences.index(i as int).len() == first_len);
        assert(forall |k: int| 0 <= k < i + 1 ==> sequences.index(k).len() == first_len);

        // This assertion follows from the previous one and transitivity
        proof {
            assert(forall |p: int, q: int| 0 <= p < i + 1 && 0 <= q < i + 1 ==> sequences.index(p).len() == sequences.index(q).len()) by {
                // To prove: forall p, q in [0, i], sequences[p].len() == sequences[q].len()
                // We know: Forall k in [0, i], sequences[k].len() == first_len
                // Let p, q be arbitrary indices such that 0 <= p < i + 1 and 0 <= q < i + 1.
                // From the invariant, we know sequences[p].len() == first_len and sequences[q].len() == first_len.
                // By transitivity of equality, sequences[p].len() == sequences[q].len().
            }
        }
        i = i + 1;
    }

    // After the loop, the invariant holds for `i == sequences.len()`.
    // Thus, for all `k` such that `0 <= k < sequences.len()`, `sequences[k].len() == first_len`.
    // This directly implies the postcondition:
    // forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len()
    // because if `sequences[i].len() == first_len` and `sequences[j].len() == first_len`, then `sequences[i].len() == sequences[j].len()`.
    assert(forall |k: int| 0 <= k < sequences.len() ==> sequences.index(k).len() == first_len);
    assert(forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences.index(i).len() == sequences.index(j).len()) by {
        // Let i, j be arbitrary integers such that 0 <= i < sequences.len() and 0 <= j < sequences.len().
        // From the loop invariant (which holds after termination), we know:
        // (sequences[i]).len() == first_len
        // (sequences[j]).len() == first_len
        // Therefore, (sequences[i]).len() == (sequences[j]).len().
    };
    true
}
// </vc-code>

fn main() {
}

}