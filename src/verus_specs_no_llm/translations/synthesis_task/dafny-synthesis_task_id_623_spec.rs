// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn PowerOfListElements(l: Seq<int>, n: int) -> (result: Seq<int>)
    requires n >= 0
    ensures result.len() == l.len(),
            forall|i: int| 0 <= i < l.len() ==> result[i] == Power(l[i], n)
{
}

}