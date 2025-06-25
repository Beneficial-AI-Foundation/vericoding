// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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
spec fn IsFirstEven(evenIndex: int, lst: Seq<int>) -> bool {
    forall i :: 0 <= i < evenIndex ==> IsOdd(lst.spec_index(i))
}
spec fn IsFirstOdd(oddIndex: int, lst: Seq<int>) -> bool {
    forall i :: 0 <= i < oddIndex ==> IsEven(lst.spec_index(i))
}

fn FirstEvenOddIndices(lst: Seq<int>) -> (evenIndex: int, oddIndex: int)
    requires
        lst.len() >= 2,
        exists i :: 0 <= i < lst.len() && IsEven(lst.spec_index(i)),
        exists i :: 0 <= i < lst.len() && IsOdd(lst.spec_index(i))
    ensures
        0 <= evenIndex < lst.len(),
        0 <= oddIndex < lst.len()
    // This is the postcondition that,
        that it's the first, not just any,
        IsEven(lst.spec_index(evenIndex)) && IsFirstEven(evenIndex, lst),
        IsOdd(lst.spec_index(oddIndex)) && IsFirstOdd(oddIndex, lst)
{
    return (0, 0);
}

}