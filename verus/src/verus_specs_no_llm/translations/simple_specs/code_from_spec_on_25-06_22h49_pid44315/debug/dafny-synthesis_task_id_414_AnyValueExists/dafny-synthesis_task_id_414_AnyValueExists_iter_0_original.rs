// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AnyValueExists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures
        result <==> (exists i :: 0 <= i < seq1.len() && seq1.spec_index(i) in seq2)
{
    return false;
}

}