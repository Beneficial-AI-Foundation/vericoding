// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}
spec fn IsFirstOdd(oddIndex: int, lst: Seq<int>) -> bool {
    forall |i: int| 0 <= i < oddIndex ==> IsEven(lst.index(i))
}
spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}
spec fn IsFirstEven(evenIndex: int, lst: Seq<int>) -> bool {
    forall |i: int| 0 <= i < evenIndex ==> IsOdd(lst.index(i))
}

spec fn spec_FirstEvenOddIndices(lst: Seq<int>) -> evenIndex: int, oddIndex : int
    requires
        lst.len() >= 2,
        exists |i: int| 0 <= i < lst.len() && IsEven(lst.index(i)),
        exists |i: int| 0 <= i < lst.len() && IsOdd(lst.index(i))
    ensures
        0 <= evenIndex < lst.len(),
        0 <= oddIndex < lst.len()
  // This is the postcondition that,
        that it's the first, not just any,
        IsEven(lst.index(evenIndex)) && IsFirstEven(evenIndex, lst),
        IsOdd(lst.index(oddIndex)) && IsFirstOdd(oddIndex, lst)
;

proof fn lemma_FirstEvenOddIndices(lst: Seq<int>) -> (evenIndex: int, oddIndex: int)
    requires
        lst.len() >= 2,
        exists |i: int| 0 <= i < lst.len() && IsEven(lst.index(i)),
        exists |i: int| 0 <= i < lst.len() && IsOdd(lst.index(i))
    ensures
        0 <= evenIndex < lst.len(),
        0 <= oddIndex < lst.len()
  // This is the postcondition that,
        that it's the first, not just any,
        IsEven(lst.index(evenIndex)) && IsFirstEven(evenIndex, lst),
        IsOdd(lst.index(oddIndex)) && IsFirstOdd(oddIndex, lst)
{
    (0, 0)
}

}