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
        assert(forall|i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len());
        return true;
    }
    
    let first_len = sequences[0].len();
    let mut idx: int = 1;
    
    while idx < sequences.len()
        invariant
            1 <= idx <= sequences.len(),
            sequences.len() > 0,
            first_len == sequences[0].len(),
            forall|k: int| 0 <= k < idx ==> sequences[k].len() == first_len
    {
        if sequences[idx].len() != first_len {
            // Found sequences with different lengths
            assert(sequences[0].len() != sequences[idx].len());
            assert(!(forall|i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len()));
            return false;
        }
        idx = idx + 1;
    }
    
    // All sequences have the same length as the first one
    assert(forall|k: int| 0 <= k < sequences.len() ==> sequences[k].len() == first_len);
    
    // Prove the postcondition
    assert forall|i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() implies sequences[i].len() == sequences[j].len() by {
        assert(sequences[i].len() == first_len);
        assert(sequences[j].len() == first_len);
    }
    
    true
}

}