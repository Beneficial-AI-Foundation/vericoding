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
    let mut even_idx: Option<int> = None;
    let mut odd_idx: Option<int> = None;
    let mut i: usize = 0;
    
    while i < lst.len() && (even_idx.is_none() || odd_idx.is_none())
        invariant
            0 <= i <= lst.len(),
            // For even_idx: if found, it's the first even in range [0, i)
            even_idx.is_some() ==> {
                let idx = even_idx.get_Some_0();
                0 <= idx < i && 
                IsEven(lst.spec_index(idx)) && 
                forall|j: int| 0 <= j < idx ==> IsOdd(lst.spec_index(j))
            },
            // For odd_idx: if found, it's the first odd in range [0, i)
            odd_idx.is_some() ==> {
                let idx = odd_idx.get_Some_0();
                0 <= idx < i && 
                IsOdd(lst.spec_index(idx)) && 
                forall|j: int| 0 <= j < idx ==> IsEven(lst.spec_index(j))
            },
            // If even_idx not found yet, no even numbers in [0, i)
            even_idx.is_none() ==> forall|j: int| 0 <= j < i ==> IsOdd(lst.spec_index(j)),
            // If odd_idx not found yet, no odd numbers in [0, i)  
            odd_idx.is_none() ==> forall|j: int| 0 <= j < i ==> IsEven(lst.spec_index(j)),
            // Preservation of existence: even/odd elements still exist somewhere
            exists|k: int| i <= k < lst.len() ==> (even_idx.is_some() || exists|m: int| k <= m < lst.len() && IsEven(lst.spec_index(m))),
            exists|k: int| i <= k < lst.len() ==> (odd_idx.is_some() || exists|m: int| k <= m < lst.len() && IsOdd(lst.spec_index(m)))
        decreases lst.len() - i
    {
        let current_val = lst.spec_index(i as int);
        
        if even_idx.is_none() && IsEven(current_val) {
            even_idx = Some(i as int);
        }
        if odd_idx.is_none() && IsOdd(current_val) {
            odd_idx = Some(i as int);
        }
        i = i + 1;
    }
    
    // Extract the indices - they must exist due to preconditions
    proof {
        // From preconditions: both even and odd elements exist in the full sequence
        // From invariants: if not found by position i, they must exist in [i, len)
        // Loop exits when both found OR i == len
        // If i == len and one not found, that contradicts the precondition
        
        if even_idx.is_none() {
            // All elements in [0, i) are odd, but an even element must exist
            // Since i == lst.len() at loop exit, this contradicts the precondition
            assert(false);
        }
        
        if odd_idx.is_none() {
            // All elements in [0, i) are even, but an odd element must exist  
            // Since i == lst.len() at loop exit, this contradicts the precondition
            assert(false);
        }
        
        assert(even_idx.is_some());
        assert(odd_idx.is_some());
    }
    
    let final_even_idx = even_idx.get_Some_0();
    let final_odd_idx = odd_idx.get_Some_0();
    
    proof {
        // Verify postconditions are satisfied
        assert(0 <= final_even_idx < lst.len());
        assert(0 <= final_odd_idx < lst.len());
        assert(IsEven(lst.spec_index(final_even_idx)));
        assert(IsOdd(lst.spec_index(final_odd_idx)));
        assert(IsFirstEven(final_even_idx, lst));
        assert(IsFirstOdd(final_odd_idx, lst));
    }
    
    (final_even_idx, final_odd_idx)
}

}