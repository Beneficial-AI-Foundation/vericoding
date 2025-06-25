// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int|0<=u<s.len() ==> s[u]>=0
}

fn mfirstNegative(v: Vec<int>) -> b: bool, i: int
    ensures b <==> exists|k: int|0<=k<v.len() and v[k]<0,
            b ==> 0<=i<v.len() and v[i]<0 and positive(v[0..i])
{
}

}