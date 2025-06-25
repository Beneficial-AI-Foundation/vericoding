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
spec fn IsFirstEven(evenIndex: int, lst: Seq<int>) -> bool {
    forall|i: int| 0 <= i < evenIndex ==> IsOdd(lst[i])
}
spec fn IsFirstOdd(oddIndex: int, lst: Seq<int>) -> bool {
    forall|i: int| 0 <= i < oddIndex ==> IsEven(lst[i])
}

fn FirstEvenOddIndices(lst: Seq<int>) -> evenIndex: int, oddIndex: int
    requires lst.len() >= 2,
             exists|i: int| 0 <= i < lst.len() and IsEven(lst[i]),
             exists|i: int| 0 <= i < lst.len() and IsOdd(lst[i])
    ensures 0 <= evenIndex < lst.len(),
            0 <= oddIndex < lst.len()
    // This is the postcondition that,
            that it's the first, not just any,
            IsEven(lst[evenIndex]) and IsFirstEven(evenIndex, lst),
            IsOdd(lst[oddIndex]) and IsFirstOdd(oddIndex, lst)
{
}

}