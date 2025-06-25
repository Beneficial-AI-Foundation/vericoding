// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AddLists(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall i :: 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) + b.spec_index(i)
{
    return Seq::empty();
}

}