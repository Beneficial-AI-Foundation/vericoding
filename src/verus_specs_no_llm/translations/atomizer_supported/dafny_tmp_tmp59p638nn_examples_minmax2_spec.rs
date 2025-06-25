// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn DifferenceMinMax(a: Vec<int>) -> (diff: int)
    requires a.len() > 0
    ensures diff == (Max(a[..]) - Min(a[..]))
{
}

}