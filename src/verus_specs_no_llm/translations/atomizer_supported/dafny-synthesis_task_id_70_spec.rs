// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn AllSequencesEqualLength(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> forall|i: int, j: int| 0 <= i < sequences.len() and 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len()
{
}

}