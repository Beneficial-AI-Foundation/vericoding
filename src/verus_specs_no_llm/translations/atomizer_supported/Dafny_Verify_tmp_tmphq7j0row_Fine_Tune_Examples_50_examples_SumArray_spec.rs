// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SumArray(arr: Vec<int>) -> (sum: int)
    requires arr.len() > 0
    ensures sum == Sum(arr, arr.len())
{
}

}