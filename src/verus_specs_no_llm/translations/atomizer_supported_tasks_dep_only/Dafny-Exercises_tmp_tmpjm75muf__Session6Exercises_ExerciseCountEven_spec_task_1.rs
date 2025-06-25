// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int|0<=u<s.len() ==> s[u]>=0
}

fn mcountEven(v: Vec<int>) -> (n: int)
    requires positive(v[..])
    ensures n==CountEven(v[..])
{
}

}