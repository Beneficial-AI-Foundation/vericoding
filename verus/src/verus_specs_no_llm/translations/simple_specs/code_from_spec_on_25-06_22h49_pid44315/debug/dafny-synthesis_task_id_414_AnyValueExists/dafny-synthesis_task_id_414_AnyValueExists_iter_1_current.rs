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
            !(exists i :: 0 <= i < j && seq1.spec_index(i) in seq2)
    {
        let value = seq1.index(j);
        if seq2.contains(value) {
            return true;
        }
        j += 1;
    }
    false
}

}