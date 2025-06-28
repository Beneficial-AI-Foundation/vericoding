// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall u::0<=u<s.len() ==> s.spec_index(u)>=0
}

fn mfirstNegative(v: Vec<int>) -> (b: bool, i: int)
    ensures
        b <==> exists k::0<=k<v.len() && v.spec_index(k)<0,
        b ==> 0<=i<v.len() && v.spec_index(i)<0 && positive(v.spec_index(0..i))
{
    return (false, 0);
}

}