use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AnyValueExists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures
        result <==> (exists i :: 0 <= i < seq1.len() && seq2.contains(seq1[i]))
{
    let mut j = 0;
    while j < seq1.len()
        invariant
            0 <= j <= seq1.len(),
            forall i :: 0 <= i < j ==> !seq2.contains(seq1[i]),
    {
        let value = seq1[j as int];
        if seq2.contains(value) {
            // When we find a value in seq2, we can prove the postcondition
            assert(seq1[j as int] == value);
            assert(seq2.contains(value));
            assert(seq2.contains(seq1[j as int]));
            assert(0 <= j < seq1.len());
            assert(exists i :: 0 <= i < seq1.len() && seq2.contains(seq1[i])) by {
                assert(seq2.contains(seq1[j as int]));
                assert(0 <= j < seq1.len());
            }
            return true;
        } else {
            // If value is not in seq2, we can strengthen our invariant
            assert(!seq2.contains(seq1[j as int]));
        }
        j += 1;
    }
    
    // At this point, we've checked all elements and none are in seq2
    assert(j == seq1.len());
    assert(forall i :: 0 <= i < seq1.len() ==> !seq2.contains(seq1[i]));
    
    // Prove that no element exists in seq2
    assert(!(exists i :: 0 <= i < seq1.len() && seq2.contains(seq1[i])));
    
    false
}

}