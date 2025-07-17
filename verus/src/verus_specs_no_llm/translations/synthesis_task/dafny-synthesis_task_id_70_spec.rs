// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AllSequencesEqualLength(sequences: Seq<Seq<int>>) -> result: bool
    ensures
        result <==> forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences.index(i).len() == sequences.index(j).len()
;

proof fn lemma_AllSequencesEqualLength(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures
        result <==> forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences.index(i).len() == sequences.index(j).len()
{
    false
}

}