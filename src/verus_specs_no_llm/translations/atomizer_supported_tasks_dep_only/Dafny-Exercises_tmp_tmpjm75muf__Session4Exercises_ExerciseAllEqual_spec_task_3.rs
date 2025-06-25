// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn allEqual(s: Seq<int>) -> bool {
    forall|i: int, j: int|0<=i<s.len() and 0<=j<s.len() ==> s[i]==s[j]
}

fn mallEqual3(v: Vec<int>) -> (b: bool)
    ensures b==allEqual(v[0..v.len()])
{
}

}