// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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