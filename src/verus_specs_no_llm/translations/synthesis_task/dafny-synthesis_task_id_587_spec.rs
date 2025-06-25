// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ArrayToSeq(a: Vec<int>) -> (s: Seq<int>)
    requires a != null
    ensures s.len() == a.len(),
            forall|i: int| 0 <= i < a.len() ==> s[i] == a[i]
{
}

}