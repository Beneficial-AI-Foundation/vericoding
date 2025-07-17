// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AnyValueExists(seq1: Seq<int>, seq2: Seq<int>) -> result: bool
    ensures
        result <==> (exists |i: int| 0 <= i < seq1.len() && seq1.index(i) in seq2)
;

proof fn lemma_AnyValueExists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures
        result <==> (exists |i: int| 0 <= i < seq1.len() && seq1.index(i) in seq2)
{
    false
}

}