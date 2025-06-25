// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn maxSeq(v: Seq<int>) -> (max: int)
    requires v.len() >= 1
    ensures forall|i: int| 0 <= i < v.len() ==> max >= v[i],
            max in v
{
}

}