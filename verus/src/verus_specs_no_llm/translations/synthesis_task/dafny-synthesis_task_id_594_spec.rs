// Translated from Dafny
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

spec fn spec_FirstEvenOddDifference(a: Vec<int>) -> diff: int
    requires
        a.len() >= 2,
        exists |i: int| 0 <= i < a.len() && IsEven(a.index(i)),
        exists |i: int| 0 <= i < a.len() && IsOdd(a.index(i))
    ensures
        exists |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && IsEven(a.index(i)) && IsOdd(a.index(j)) && diff == a.index(i) - a.index(j) && 
        (forall |k: int| 0 <= k < i ==> IsOdd(a.index(k))) && (forall |k: int| 0 <= k < j ==> IsEven(a.index(k)))
;

proof fn lemma_FirstEvenOddDifference(a: Vec<int>) -> (diff: int)
    requires
        a.len() >= 2,
        exists |i: int| 0 <= i < a.len() && IsEven(a.index(i)),
        exists |i: int| 0 <= i < a.len() && IsOdd(a.index(i))
    ensures
        exists |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && IsEven(a.index(i)) && IsOdd(a.index(j)) && diff == a.index(i) - a.index(j) && 
        (forall |k: int| 0 <= k < i ==> IsOdd(a.index(k))) && (forall |k: int| 0 <= k < j ==> IsEven(a.index(k)))
{
    0
}

}