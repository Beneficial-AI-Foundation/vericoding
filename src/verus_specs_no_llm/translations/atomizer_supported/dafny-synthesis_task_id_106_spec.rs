// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn AppendArrayToSeq(s: Seq<int>, a: Vec<int>) -> (r: Seq<int>)
    requires a != null
    ensures r.len() == s.len() + a.len(),
            forall|i: int| 0 <= i < s.len() ==> r[i] == s[i],
            forall|i: int| 0 <= i < a.len() ==> r[s.len() + i] == a[i]
{
}

}