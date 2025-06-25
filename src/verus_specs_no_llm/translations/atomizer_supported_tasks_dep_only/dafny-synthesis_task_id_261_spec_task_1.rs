// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ElementWiseDivision(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires a.len() == b.len(),
             forall|i: int| 0 <= i < b.len() ==> b[i] != 0
    ensures result.len() == a.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i]
{
}

}