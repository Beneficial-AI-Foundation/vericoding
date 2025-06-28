// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArrayToSeq(a: Vec<int>) -> (s: Seq<int>)
    requires
        a != null
    ensures
        s.len() == a.len(),
        forall i :: 0 <= i < a.len() ==> s.spec_index(i) == a.spec_index(i)
{
    return Seq::empty();
}

}