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
                let idx = even_idx.unwrap();
                0 <= idx < i && 
                IsEven(lst.spec_index(idx as int)) && 
                IsFirstEven(idx as int, lst)
            },
            // For odd_idx: if found, it's the first odd in range [0, i)
            odd_idx.is_some() ==> {
                let idx = odd_idx.unwrap();
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
        }
        if odd_idx.is_none() && IsOdd(current_val) {
            odd_idx = Some(i);
        }
        i = i + 1;
    }
    
    // Extract the indices using pattern matching
    let final_even_idx = match even_idx {
        Some(idx) => idx as int,
        None => {
            // This case is impossible due to preconditions
            assert(false);
            0
        }
    };
    
    let final_odd_idx = match odd_idx {
        Some(idx) => idx as int,
        None => {
            // This case is impossible due to preconditions
            assert(false);
            0
        }
    };
    
    (final_even_idx, final_odd_idx)
}

}