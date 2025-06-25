// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ArraySum(a: Vec<int>) -> (result: int)
    ensures result == sumTo(a, a.len())
{
}

}