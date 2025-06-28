// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AppendArrayToSeq(s: Seq<int>, a: Vec<int>) -> (r: Seq<int>)
    requires
        a != null
    ensures
        r.len() == s.len() + a.len(),
        forall i :: 0 <= i < s.len() ==> r.spec_index(i) == s.spec_index(i),
        forall i :: 0 <= i < a.len() ==> r.spec_index(s.len() + i) == a.spec_index(i)
{
    return Seq::empty();
}

}