use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AnyValueExists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures
        result <==> (exists i :: 0 <= i < seq1.len() && seq1.spec_index(i) in seq2)
{
    let mut j = 0;
    while j < seq1.len()
        invariant
            0 <= j <= seq1.len(),
            forall i :: 0 <= i < j ==> !(seq1.spec_index(i) in seq2)
    {
        let value = seq1.spec_index(j as int);
        if seq2.contains(value) {
            assert(seq1.spec_index(j as int) in seq2);
            assert(0 <= j < seq1.len());
            return true;
        }
        j += 1;
    }
    
    // At this point, we've checked all elements and none are in seq2
    assert(j == seq1.len());
    assert(forall i :: 0 <= i < seq1.len() ==> !(seq1.spec_index(i) in seq2));
    
    // Prove that no element exists in seq2
    assert(!(exists i :: 0 <= i < seq1.len() && seq1.spec_index(i) in seq2));
    
    false
}

}