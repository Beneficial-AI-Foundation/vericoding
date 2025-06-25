// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}
spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}

fn FirstEvenOddDifference(a: Vec<int>) -> (diff: int)
    requires
        a.len() >= 2,
        exists i :: 0 <= i < a.len() && IsEven(a.spec_index(i)),
        exists i :: 0 <= i < a.len() && IsOdd(a.spec_index(i))
    ensures
        exists i, j :: 0 <= i < a.len() && 0 <= j < a.len() && IsEven(a.spec_index(i)) && IsOdd(a.spec_index(j)) && diff == a.spec_index(i) - a.spec_index(j) && 
        (forall k :: 0 <= k < i ==> IsOdd(a.spec_index(k))) && (forall k :: 0 <= k < j ==> IsEven(a.spec_index(k)))
{
    return 0;
}

}