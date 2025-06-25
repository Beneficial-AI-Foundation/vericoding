// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn AddLists(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires a.len() == b.len()
    ensures result.len() == a.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] + b[i]
{
}

}