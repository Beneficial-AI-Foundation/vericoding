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
spec fn IsFirstOdd(oddIndex: int, lst: Seq<int>) -> bool {
    forall i :: 0 <= i < oddIndex ==> IsEven(lst.spec_index(i))
}
spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}
spec fn IsFirstEven(evenIndex: int, lst: Seq<int>) -> bool {
    forall i :: 0 <= i < evenIndex ==> IsOdd(lst.spec_index(i))
}

fn FirstEvenOddIndices(lst: Seq<int>) -> (evenIndex: int, oddIndex: int)
    requires
        lst.len() >= 2,
        exists i :: 0 <= i < lst.len() && IsEven(lst.spec_index(i)),
        exists i :: 0 <= i < lst.len() && IsOdd(lst.spec_index(i))
    ensures
        0 <= evenIndex < lst.len(),
        0 <= oddIndex < lst.len(),
        IsEven(lst.spec_index(evenIndex)) && IsFirstEven(evenIndex, lst),
        IsOdd(lst.spec_index(oddIndex)) && IsFirstOdd(oddIndex, lst)
{
    let mut even_idx: int = -1;
    let mut odd_idx: int = -1;
    let mut i: int = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            even_idx == -1 ==> forall j :: 0 <= j < i ==> IsOdd(lst.spec_index(j)),
            even_idx >= 0 ==> (0 <= even_idx < i && IsEven(lst.spec_index(even_idx)) && IsFirstEven(even_idx, lst)),
            odd_idx == -1 ==> forall j :: 0 <= j < i ==> IsEven(lst.spec_index(j)),
            odd_idx >= 0 ==> (0 <= odd_idx < i && IsOdd(lst.spec_index(odd_idx)) && IsFirstOdd(odd_idx, lst))
    {
        if even_idx == -1 && IsEven(lst.spec_index(i)) {
            even_idx = i;
        }
        if odd_idx == -1 && IsOdd(lst.spec_index(i)) {
            odd_idx = i;
        }
        if even_idx >= 0 && odd_idx >= 0 {
            break;
        }
        i = i + 1;
    }
    
    // The preconditions guarantee these exist
    assert(even_idx >= 0);
    assert(odd_idx >= 0);
    
    (even_idx, odd_idx)
}

}