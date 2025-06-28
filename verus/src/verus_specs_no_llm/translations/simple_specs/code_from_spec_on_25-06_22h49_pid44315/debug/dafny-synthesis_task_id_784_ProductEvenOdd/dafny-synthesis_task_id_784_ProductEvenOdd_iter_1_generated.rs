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

spec fn IsFirstEven(evenIndex: int, lst: Seq<int>) -> bool {
    forall|i: int| 0 <= i < evenIndex ==> IsOdd(lst.spec_index(i))
}

spec fn IsFirstOdd(oddIndex: int, lst: Seq<int>) -> bool {
    forall|i: int| 0 <= i < oddIndex ==> IsEven(lst.spec_index(i))
}

fn FirstEvenOddIndices(lst: Seq<int>) -> (evenIndex: int, oddIndex: int)
    requires 
        lst.len() >= 2,
        exists|i: int| 0 <= i < lst.len() && IsEven(lst.spec_index(i)),
        exists|i: int| 0 <= i < lst.len() && IsOdd(lst.spec_index(i))
    ensures 
        0 <= evenIndex < lst.len(),
        0 <= oddIndex < lst.len(),
        IsEven(lst.spec_index(evenIndex)) && IsFirstEven(evenIndex, lst),
        IsOdd(lst.spec_index(oddIndex)) && IsFirstOdd(oddIndex, lst)
{
    let mut even_idx = 0;
    let mut odd_idx = 0;
    
    // Find first even index
    let mut i = 0;
    while i < lst.len()
        invariant 
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i ==> IsOdd(lst.spec_index(j))
        decreases lst.len() - i
    {
        if IsEven(lst.spec_index(i)) {
            even_idx = i;
            break;
        }
        i = i + 1;
    }
    
    // Find first odd index
    let mut j = 0;
    while j < lst.len()
        invariant 
            0 <= j <= lst.len(),
            forall|k: int| 0 <= k < j ==> IsEven(lst.spec_index(k))
        decreases lst.len() - j
    {
        if IsOdd(lst.spec_index(j)) {
            odd_idx = j;
            break;
        }
        j = j + 1;
    }
    
    (even_idx, odd_idx)
}

}