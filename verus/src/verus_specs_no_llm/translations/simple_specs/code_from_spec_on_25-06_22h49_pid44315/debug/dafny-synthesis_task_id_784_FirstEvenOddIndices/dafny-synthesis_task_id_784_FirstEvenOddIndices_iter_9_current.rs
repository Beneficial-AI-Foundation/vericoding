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
    let mut even_idx: Option<usize> = None;
    let mut odd_idx: Option<usize> = None;
    let mut i: usize = 0;
    
    while i < lst.len() && (even_idx.is_none() || odd_idx.is_none())
        invariant
            0 <= i <= lst.len(),
            // For even_idx: if found, it's the first even in range [0, i)
            even_idx.is_some() ==> {
                let idx = even_idx.get_Some_0();
                0 <= idx < i && 
                IsEven(lst.spec_index(idx as int)) && 
                IsFirstEven(idx as int, lst)
            },
            // For odd_idx: if found, it's the first odd in range [0, i)
            odd_idx.is_some() ==> {
                let idx = odd_idx.get_Some_0();
                0 <= idx < i && 
                IsOdd(lst.spec_index(idx as int)) && 
                IsFirstOdd(idx as int, lst)
            },
            // If even_idx not found yet, no even numbers in [0, i)
            even_idx.is_none() ==> forall|j: int| 0 <= j < i ==> IsOdd(lst.spec_index(j)),
            // If odd_idx not found yet, no odd numbers in [0, i)  
            odd_idx.is_none() ==> forall|j: int| 0 <= j < i ==> IsEven(lst.spec_index(j)),
            // From preconditions: even and odd elements exist in the full sequence
            exists|k: int| 0 <= k < lst.len() && IsEven(lst.spec_index(k)),
            exists|k: int| 0 <= k < lst.len() && IsOdd(lst.spec_index(k))
        decreases lst.len() - i
    {
        let current_val = lst.spec_index(i as int);
        
        if even_idx.is_none() && IsEven(current_val) {
            even_idx = Some(i);
            
            // Prove that this is the first even index
            assert(forall|j: int| 0 <= j < i ==> IsOdd(lst.spec_index(j))) by {
                // This follows from the invariant
            };
            assert(IsFirstEven(i as int, lst)) by {
                // This follows from the definition and the above assertion
            };
        }
        if odd_idx.is_none() && IsOdd(current_val) {
            odd_idx = Some(i);
            
            // Prove that this is the first odd index  
            assert(forall|j: int| 0 <= j < i ==> IsEven(lst.spec_index(j))) by {
                // This follows from the invariant
            };
            assert(IsFirstOdd(i as int, lst)) by {
                // This follows from the definition and the above assertion
            };
        }
        i = i + 1;
    }
    
    // Extract the indices - they must exist due to preconditions
    assert(even_idx.is_some()) by {
        if even_idx.is_none() {
            // All elements in [0, len) are odd, but an even element must exist
            assert(i == lst.len());
            assert(forall|j: int| 0 <= j < lst.len() ==> IsOdd(lst.spec_index(j)));
            assert(exists|k: int| 0 <= k < lst.len() && IsEven(lst.spec_index(k)));
            // This is a contradiction - we can't have all elements odd and some element even
            assert(false);
        }
    };
    
    assert(odd_idx.is_some()) by {
        if odd_idx.is_none() {
            // All elements in [0, len) are even, but an odd element must exist  
            assert(i == lst.len());
            assert(forall|j: int| 0 <= j < lst.len() ==> IsEven(lst.spec_index(j)));
            assert(exists|k: int| 0 <= k < lst.len() && IsOdd(lst.spec_index(k)));
            // This is a contradiction - we can't have all elements even and some element odd
            assert(false);
        }
    };
    
    let final_even_idx = even_idx.get_Some_0() as int;
    let final_odd_idx = odd_idx.get_Some_0() as int;
    
    (final_even_idx, final_odd_idx)
}

}