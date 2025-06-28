// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall x :: x in diff <==> (x in a && x !in b),
        forall i, j :: 0 <= i < j < diff.len() ==> diff.spec_index(i) != diff.spec_index(j)
{
    return Seq::empty();
}

}