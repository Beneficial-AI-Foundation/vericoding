// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsSmaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires a.len() == b.len()
    ensures result <==> forall|i: int| 0 <= i < a.len() ==> a[i] > b[i],
            !result <==> exists|i: int| 0 <= i < a.len() and a[i] <= b[i]
{
}

}