// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn maxArray(arr: Vec<int>) -> (max: int)
    requires arr.len() > 0
    ensures forall i: int :: 0 <= i < arr.len() ==> arr[i] <= max,
            exists|x: int|0 <= x < arr.len() and arr[x] == max
{
}

}