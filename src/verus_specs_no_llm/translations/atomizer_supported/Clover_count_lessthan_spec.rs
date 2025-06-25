// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CountLessThan(numbers: set<int>, threshold: int) -> (count: int)
    ensures count == set i .len() i in numbers and i < threshold|
{
}

}