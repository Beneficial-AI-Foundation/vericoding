// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SumInRange(a: Vec<int>, start: int, end: int) -> (sum: int)
    requires a != null,
             0 <= start and start <= end and end <= a.len()
    ensures sum == sumTo(a, start, end)
{
}

}