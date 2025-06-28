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
            exists|k: int| 0 <= k < lst.len() && IsEven(lst.spec_index(k)),
            i < lst.len() ==> exists|k: int| i <= k < lst.len() && IsEven(lst.spec_index(k))
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
            exists|m: int| 0 <= m < lst.len() && IsOdd(lst.spec_index(m)),
            j < lst.len() ==> exists|m: int| j <= m < lst.len() && IsOdd(lst.spec_index(m))
        decreases lst.len() - j
    {
        if lst[j as int] % 2 != 0 {
            break;
        }
        j = j + 1;
    }
    let odd_idx = j;
    
    // Prove that indices are in bounds
    assert(even_idx < lst.len()) by {
        // The loop terminates because we know an even element exists
        // and we break when we find it
        assert(exists|k: int| 0 <= k < lst.len() && IsEven(lst.spec_index(k)));
    };
    
    assert(odd_idx < lst.len()) by {
        // The loop terminates because we know an odd element exists
        // and we break when we find it
        assert(exists|m: int| 0 <= m < lst.len() && IsOdd(lst.spec_index(m)));
    };
    
    // Prove the elements at found indices have correct parity
    assert(IsEven(lst.spec_index(even_idx as int))) by {
        assert(lst[even_idx as int] % 2 == 0);
        assert(lst.spec_index(even_idx as int) == lst[even_idx as int]);
    };
    
    assert(IsOdd(lst.spec_index(odd_idx as int))) by {
        assert(lst[odd_idx as int] % 2 != 0);
        assert(lst.spec_index(odd_idx as int) == lst[odd_idx as int]);
    };
    
    // These follow from the loop invariants
    assert(IsFirstEven(even_idx as int, lst));
    assert(IsFirstOdd(odd_idx as int, lst));
    
    (even_idx as int, odd_idx as int)
}

}