use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AllSequencesEqualLength(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures
        result <==> (forall|i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
{
    if sequences.len() == 0 {
        // Empty sequence case - vacuously true
        return true;
    }
    
    let first_len = sequences[0].len();
    let mut idx: usize = 1;
    
    while idx < sequences.len()
        invariant
            1 <= idx <= sequences.len(),
            sequences.len() > 0,
            first_len == sequences[0].len(),
            forall|k: int| 0 <= k < idx ==> sequences[k].len() == first_len,
            // Key invariant: all checked sequences so far have equal lengths pairwise
            forall|i: int, j: int| 0 <= i < idx && 0 <= j < idx ==> sequences[i].len() == sequences[j].len()
        decreases sequences.len() - idx
    {
        if sequences[idx as int].len() != first_len {
            // Found sequences with different lengths
            assert(sequences[0].len() == first_len);
            assert(sequences[idx as int].len() != first_len);
            assert(sequences[0].len() != sequences[idx as int].len());
            assert(0 <= 0 < sequences.len() && 0 <= (idx as int) < sequences.len());
            // This witnesses that not all pairs have equal length
            return false;
        }
        idx = idx + 1;
    }
    
    // All sequences have the same length as the first one
    assert(idx == sequences.len());
    assert(forall|k: int| 0 <= k < sequences.len() ==> sequences[k].len() == first_len);
    
    // Prove the postcondition for the true case
    assert(forall|i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> {
        sequences[i].len() == first_len && sequences[j].len() == first_len
    }) by {
        // This follows from the loop invariant extended to the full range
    };
    
    true
}

}