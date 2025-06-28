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
    // Find first even index
    let mut i: usize = 0;
    while i < lst.len()
        invariant 
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i ==> IsOdd(lst.spec_index(j)),
            exists|k: int| (i as int) <= k < lst.len() && IsEven(lst.spec_index(k))
        decreases lst.len() - i
    {
        if lst[i as int] % 2 == 0 {
            break;
        }
        i = i + 1;
    }
    let even_idx = i;
    
    // Find first odd index
    let mut j: usize = 0;
    while j < lst.len()
        invariant 
            0 <= j <= lst.len(),
            forall|k: int| 0 <= k < j ==> IsEven(lst.spec_index(k)),
            exists|m: int| (j as int) <= m < lst.len() && IsOdd(lst.spec_index(m))
        decreases lst.len() - j
    {
        if lst[j as int] % 2 != 0 {
            break;
        }
        j = j + 1;
    }
    let odd_idx = j;
    
    // Prove that the loops terminated because they found the required elements
    proof {
        // For the even case: we know an even element exists, and we either found it or 
        // would have continued until we did
        assert(even_idx < lst.len()) by {
            if even_idx == lst.len() {
                // This would contradict our precondition that an even element exists
                // and our loop invariant that one exists at or after position i
                assert(false);
            }
        };
        
        // For the odd case: similar reasoning
        assert(odd_idx < lst.len()) by {
            if odd_idx == lst.len() {
                // This would contradict our precondition that an odd element exists
                // and our loop invariant that one exists at or after position j
                assert(false);
            }
        };
    }
    
    // The elements at the found indices have the correct parity
    assert(IsEven(lst.spec_index(even_idx as int)));
    assert(IsOdd(lst.spec_index(odd_idx as int)));
    
    // These follow from the loop invariants
    assert(IsFirstEven(even_idx as int, lst));
    assert(IsFirstOdd(odd_idx as int, lst));
    
    (even_idx as int, odd_idx as int)
}

}