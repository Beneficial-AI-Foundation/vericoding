// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AllSequencesEqualLength(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures
        result <==> forall i, j :: 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences.spec_index(i).len() == sequences.spec_index(j).len()
{
    return false;
}

}