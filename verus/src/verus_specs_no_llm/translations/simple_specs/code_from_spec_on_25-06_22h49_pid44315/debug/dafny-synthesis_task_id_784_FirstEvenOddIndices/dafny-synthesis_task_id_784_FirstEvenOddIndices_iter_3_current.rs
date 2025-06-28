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
    
    // After the loop, we must have found both indices
    // This follows from the preconditions and loop invariants
    proof {
        // The loop terminates when either:
        // 1. We've examined all elements (i == lst.len()), or
        // 2. We've found both indices (even_idx != -1 && odd_idx != -1)
        
        // From preconditions, we know both even and odd elements exist
        // If we examined all elements and didn't find one, that would contradict
        // the invariants combined with the existence preconditions
        
        assert(even_idx >= 0);
        assert(odd_idx >= 0);
        assert(0 <= even_idx < lst.len());
        assert(0 <= odd_idx < lst.len());
        assert(IsEven(lst.spec_index(even_idx)));
        assert(IsOdd(lst.spec_index(odd_idx)));
        assert(IsFirstEven(even_idx, lst));
        assert(IsFirstOdd(odd_idx, lst));
    }
    
    (even_idx, odd_idx)
}

}