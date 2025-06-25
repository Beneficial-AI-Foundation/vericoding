// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}
spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}

fn FirstEvenOddDifference(a: Vec<int>) -> (diff: int)
    requires a.len() >= 2,
             exists|i: int| 0 <= i < a.len() and IsEven(a[i]),
             exists|i: int| 0 <= i < a.len() and IsOdd(a[i])
    ensures exists|i: int, j: int| 0 <= i < a.len() and 0 <= j < a.len() and IsEven(a[i]) and IsOdd(a[j]) and diff == a[i] - a[j] and 
        (forall|k: int| 0 <= k < i ==> IsOdd(a[k])) and (forall|k: int| 0 <= k < j ==> IsEven(a[k]))
{
}

}