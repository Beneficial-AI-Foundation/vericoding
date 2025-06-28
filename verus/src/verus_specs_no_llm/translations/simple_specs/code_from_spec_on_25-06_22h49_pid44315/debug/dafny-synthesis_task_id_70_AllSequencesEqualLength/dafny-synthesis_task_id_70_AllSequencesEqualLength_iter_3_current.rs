use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AllSequencesEqualLength(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures
        result <==> forall i, j :: 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences.spec_index(i).len() == sequences.spec_index(j).len()
{
    if sequences.len() == 0 {
        return true;
    }
    
    let first_len = sequences.spec_index(0).len();
    let mut idx: usize = 1;
    
    while idx < sequences.len()
        invariant
            0 <= idx <= sequences.len(),
            sequences.len() > 0,
            first_len == sequences.spec_index(0).len(),
            forall k: int :: 0 <= k < idx ==> sequences.spec_index(k).len() == first_len
    {
        if sequences.spec_index(idx as int).len() != first_len {
            // Proof that when we return false, the postcondition holds
            proof {
                assert(sequences.spec_index(0).len() != sequences.spec_index(idx as int).len());
                assert(!(forall i, j :: 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences.spec_index(i).len() == sequences.spec_index(j).len()));
            }
            return false;
        }
        idx = idx + 1;
    }
    
    // Proof that when we return true, all sequences have equal length
    proof {
        assert(forall k: int :: 0 <= k < sequences.len() ==> sequences.spec_index(k).len() == first_len);
        assert forall|i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() implies sequences.spec_index(i).len() == sequences.spec_index(j).len() by {
            assert(sequences.spec_index(i).len() == first_len);
            assert(sequences.spec_index(j).len() == first_len);
        };
    }
    
    true
}

}