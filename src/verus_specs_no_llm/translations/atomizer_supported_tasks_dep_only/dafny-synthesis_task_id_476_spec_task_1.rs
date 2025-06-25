// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SumMinMax(a: Vec<int>) -> (sum: int)
    requires a.len() > 0
    ensures sum == Max(a[..]) + Min(a[..])
{
}

}