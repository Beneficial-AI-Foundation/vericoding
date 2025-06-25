// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn RotateRight(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires n >= 0
    ensures r.len() == l.len(),
            forall|i: int| 0 <= i < l.len() ==> r[i] == l[(i - n + l.len()) % l.len()]
{
}

}