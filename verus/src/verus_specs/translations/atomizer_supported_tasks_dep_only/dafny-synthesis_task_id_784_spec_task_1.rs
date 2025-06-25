use vstd::prelude::*;

verus! {

spec fn IsEven(n: int) -> bool
{
    n % 2 == 0
}

spec fn IsOdd(n: int) -> bool
{
    n % 2 != 0
}

spec fn IsFirstEven(evenIndex: int, lst: Seq<int>) -> bool
    recommends
        0 <= evenIndex < lst.len(),
        IsEven(lst[evenIndex])
{
    forall|i: int| 0 <= i < evenIndex ==> IsOdd(lst[i])
}

spec fn IsFirstOdd(oddIndex: int, lst: Seq<int>) -> bool
    recommends
        0 <= oddIndex < lst.len(),
        IsOdd(lst[oddIndex])
{
    forall|i: int| 0 <= i < oddIndex ==> IsEven(lst[i])
}

pub fn FirstEvenOddIndices(lst: Seq<int>) -> (evenIndex: int, oddIndex: int)
    requires(
        lst.len() >= 2,
        exists|i: int| 0 <= i < lst.len() && IsEven(lst[i]),
        exists|i: int| 0 <= i < lst.len() && IsOdd(lst[i])
    )
    ensures(|ret: (int, int)|
        0 <= ret.0 < lst.len() &&
        0 <= ret.1 < lst.len() &&
        IsEven(lst[ret.0]) && IsFirstEven(ret.0, lst) &&
        IsOdd(lst[ret.1]) && IsFirstOdd(ret.1, lst)
    )
{
}

}