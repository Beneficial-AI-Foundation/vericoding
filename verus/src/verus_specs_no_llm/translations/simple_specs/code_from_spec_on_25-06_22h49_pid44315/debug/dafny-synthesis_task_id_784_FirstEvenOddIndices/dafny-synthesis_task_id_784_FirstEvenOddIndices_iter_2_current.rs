use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

spec fn IsFirstOdd(oddIndex: int, lst: Seq<int>) -> bool {
    forall|i: int| 0 <= i < oddIndex ==> IsEven(lst.spec_index(i))
}

spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}

spec fn IsFirstEven(evenIndex: int, lst: Seq<int>) -> bool {
    forall|i: int| 0 <= i < evenIndex ==> IsOdd(lst.spec_index(i))
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
    let mut even_idx: int = -1;
    let mut odd_idx: int = -1;
    let mut i: int = 0;
    
    while i < lst.len() && (even_idx == -1 || odd_idx == -1)
        invariant
            0 <= i <= lst.len(),
            // For even_idx
            even_idx == -1 ==> forall|j: int| 0 <= j < i ==> IsOdd(lst.spec_index(j)),
            even_idx >= 0 ==> (
                0 <= even_idx < i && 
                IsEven(lst.spec_index(even_idx)) && 
                forall|j: int| 0 <= j < even_idx ==> IsOdd(lst.spec_index(j))
            ),
            // For odd_idx
            odd_idx == -1 ==> forall|j: int| 0 <= j < i ==> IsEven(lst.spec_index(j)),
            odd_idx >= 0 ==> (
                0 <= odd_idx < i && 
                IsOdd(lst.spec_index(odd_idx)) && 
                forall|j: int| 0 <= j < odd_idx ==> IsEven(lst.spec_index(j))
            )
    {
        if even_idx == -1 && IsEven(lst.spec_index(i)) {
            even_idx = i;
        }
        if odd_idx == -1 && IsOdd(lst.spec_index(i)) {
            odd_idx = i;
        }
        i = i + 1;
    }
    
    // Prove that we found both indices using the preconditions
    assert(even_idx >= 0) by {
        // From precondition: exists i such that lst[i] is even
        // From invariant: if even_idx == -1, then all elements up to i are odd
        // Since we've searched the entire list and there exists an even element, 
        // we must have found it
    };
    
    assert(odd_idx >= 0) by {
        // From precondition: exists i such that lst[i] is odd
        // From invariant: if odd_idx == -1, then all elements up to i are even
        // Since we've searched the entire list and there exists an odd element,
        // we must have found it
    };
    
    // Prove the "first" properties
    assert(IsFirstEven(even_idx, lst)) by {
        // From invariant: forall j < even_idx ==> IsOdd(lst[j])
        // This is exactly the definition of IsFirstEven
    };
    
    assert(IsFirstOdd(odd_idx, lst)) by {
        // From invariant: forall j < odd_idx ==> IsEven(lst[j])
        // This is exactly the definition of IsFirstOdd
    };
    
    (even_idx, odd_idx)
}

}