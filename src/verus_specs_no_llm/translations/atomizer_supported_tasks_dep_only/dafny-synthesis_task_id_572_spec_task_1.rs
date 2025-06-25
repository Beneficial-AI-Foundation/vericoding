// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn RemoveDuplicates(a: Vec<int>) -> (result: Seq<int>)
    requires a != null
    ensures forall|x: int| x in result <==> exists|i: int| 0 <= i < a.len() and a[i] == x,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
{
}

}