// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveDuplicates(a: Vec<int>) -> (result: Seq<int>)
    requires
        a != null
    ensures
        forall x :: x in result <==> exists i :: 0 <= i < a.len() && a.spec_index(i) == x,
        forall i, j :: 0 <= i < j < result.len() ==> result.spec_index(i) != result.spec_index(j)
{
    return Seq::empty();
}

}