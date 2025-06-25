// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures forall|x: int| x in diff <==> (x in a and x !in b),
            forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff[i] != diff[j]
{
}

}