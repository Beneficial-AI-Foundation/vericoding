// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SumOfCommonDivisors(a: int, b: int) -> (sum: int)
    requires a > 0 and b > 0
    ensures sum >= 0,
            forall|d: int| 1 <= d <= a and 1 <= d <= b and a % d == 0 and b % d == 0 ==> sum >= d
{
}

}