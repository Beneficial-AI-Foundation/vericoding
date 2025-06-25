// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CountArrays(arrays: Seq<Vec<int>>) -> (count: int)
    ensures count >= 0,
            count == arrays.len()
{
}

}