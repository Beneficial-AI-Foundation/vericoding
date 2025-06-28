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
    let mut even_idx: usize = 0;
    let mut odd_idx: usize = 0;
    
    // Find first even index
    let mut i: usize = 0;
    while i < lst.len() && lst[i] % 2 != 0
        invariant 
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < i ==> IsOdd(lst.spec_index(j))
        decreases lst.len() - i
    {
        i = i + 1;
    }
    even_idx = i;
    
    // Find first odd index
    let mut j: usize = 0;
    while j < lst.len() && lst[j] % 2 == 0
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
        // From precondition, there exists an even element
        assert(exists|idx: int| 0 <= idx < lst.len() && IsEven(lst.spec_index(idx)));
        // The loop terminates when we find the first even or reach the end
        // Since an even exists and we haven't reached the end, we found it
        if even_idx == lst.len() {
            // This would contradict the existence of an even element
            // since all elements 0..even_idx are odd by the loop invariant
            assert(forall|k: int| 0 <= k < even_idx ==> IsOdd(lst.spec_index(k)));
            assert(false); // contradiction
        }
    };
    
    assert(odd_idx < lst.len()) by {
        // From precondition, there exists an odd element
        assert(exists|idx: int| 0 <= idx < lst.len() && IsOdd(lst.spec_index(idx)));
        // Similar reasoning as above
        if odd_idx == lst.len() {
            assert(forall|k: int| 0 <= k < odd_idx ==> IsEven(lst.spec_index(k)));
            assert(false); // contradiction
        }
    };
    
    // Proof that the found elements are even/odd
    assert(IsEven(lst.spec_index(even_idx as int))) by {
        // Loop exited because lst[even_idx] % 2 == 0, which means IsEven
        assert(lst[even_idx] % 2 == 0);
        assert(lst[even_idx] == lst.spec_index(even_idx as int));
    };
    
    assert(IsOdd(lst.spec_index(odd_idx as int))) by {
        // Loop exited because lst[odd_idx] % 2 != 0, which means IsOdd
        assert(lst[odd_idx] % 2 != 0);
        assert(lst[odd_idx] == lst.spec_index(odd_idx as int));
    };
    
    // Proof that these are the first occurrences
    assert(IsFirstEven(even_idx as int, lst)) by {
        // The loop invariant ensures all elements before even_idx are odd
        assert(forall|k: int| 0 <= k < even_idx ==> IsOdd(lst.spec_index(k)));
    };
    
    assert(IsFirstOdd(odd_idx as int, lst)) by {
        // The loop invariant ensures all elements before odd_idx are even
        assert(forall|k: int| 0 <= k < odd_idx ==> IsEven(lst.spec_index(k)));
    };
    
    (even_idx as int, odd_idx as int)
}

}