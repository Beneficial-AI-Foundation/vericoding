// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSmaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires
        a.len() == b.len()
    ensures
        result <==> forall i :: 0 <= i < a.len() ==> a.spec_index(i) > b.spec_index(i),
        !result <==> exists i :: 0 <= i < a.len() && a.spec_index(i) <= b.spec_index(i)
{
    return false;
}

}