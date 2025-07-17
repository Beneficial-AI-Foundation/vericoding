// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int|0<=u<s.len() ==> s.index(u)>=0
}

spec fn spec_mfirstNegative(v: Vec<int>) -> b:bool, i:int
    ensures
        b <==> exists |k: int|0<=k<v.len() && v.index(k)<0,
        b ==> 0<=i<v.len() && v.index(i)<0 && positive(v.index(0..i))
;

proof fn lemma_mfirstNegative(v: Vec<int>) -> (b: bool, i: int)
    ensures
        b <==> exists |k: int|0<=k<v.len() && v.index(k)<0,
        b ==> 0<=i<v.len() && v.index(i)<0 && positive(v.index(0..i))
{
    (false, 0)
}

}