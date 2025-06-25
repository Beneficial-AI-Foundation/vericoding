// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int|0<=u<s.len() ==> s[u]>=0
}

fn mpositivertl(v: Vec<int>) -> (b: bool)
    ensures b==positive(v[0..v.len()])
{
}

}