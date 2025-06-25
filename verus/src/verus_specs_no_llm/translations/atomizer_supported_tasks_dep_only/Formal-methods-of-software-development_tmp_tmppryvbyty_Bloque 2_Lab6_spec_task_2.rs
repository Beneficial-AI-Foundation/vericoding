// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn maxSeq(v: Seq<int>) -> (max: int)
    requires
        v.len() >= 1
    ensures
        forall i :: 0 <= i < v.len() ==> max >= v.spec_index(i),
        max in v
{
    return 0;
}

}