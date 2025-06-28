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
    while i < lst.len() && !IsEven(lst.spec_index(i))
        invariant 
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i ==> IsOdd(lst.spec_index(j))
        decreases lst.len() - i
    {
        i = i + 1;
    }
    even_idx = i;
    
    // Find first odd index
    let mut j = 0;
    while j < lst.len() && !IsOdd(lst.spec_index(j))
        invariant 
            0 <= j <= lst.len(),
            forall|k: int| 0 <= k < j ==> IsEven(lst.spec_index(k))
        decreases lst.len() - j
    {
        j = j + 1;
    }
    odd_idx = j;
    
    // Proof that we found valid indices
    assert(even_idx < lst.len()) by {
        // The precondition guarantees an even element exists
        assert(exists|idx: int| 0 <= idx < lst.len() && IsEven(lst.spec_index(idx)));
    };
    
    assert(odd_idx < lst.len()) by {
        // The precondition guarantees an odd element exists
        assert(exists|idx: int| 0 <= idx < lst.len() && IsOdd(lst.spec_index(idx)));
    };
    
    // Proof that these are the first occurrences
    assert(IsFirstEven(even_idx, lst)) by {
        // The loop invariant ensures all elements before even_idx are odd
    };
    
    assert(IsFirstOdd(odd_idx, lst)) by {
        // The loop invariant ensures all elements before odd_idx are even
    };
    
    (even_idx, odd_idx)
}

}