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
            // For even_idx
            even_idx.is_none() ==> forall|j: int| 0 <= j < i ==> IsOdd(lst.spec_index(j)),
            even_idx.is_some() ==> {
                let idx = even_idx.get_Some_0();
                0 <= idx < i && 
                IsEven(lst.spec_index(idx)) && 
                forall|j: int| 0 <= j < idx ==> IsOdd(lst.spec_index(j))
            },
            // For odd_idx
            odd_idx.is_none() ==> forall|j: int| 0 <= j < i ==> IsEven(lst.spec_index(j)),
            odd_idx.is_some() ==> {
                let idx = odd_idx.get_Some_0();
                0 <= idx < i && 
                IsOdd(lst.spec_index(idx)) && 
                forall|j: int| 0 <= j < idx ==> IsEven(lst.spec_index(j))
            }
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
    let final_even_idx = even_idx.unwrap();
    let final_odd_idx = odd_idx.unwrap();
    
    proof {
        // The loop terminates when either:
        // 1. We've examined all elements (i == lst.len()), or
        // 2. We've found both indices
        
        // From preconditions, we know both even and odd elements exist
        // The invariants ensure that if we haven't found an index yet,
        // all elements examined so far have the opposite parity
        
        // If we reach the end without finding both, that would contradict
        // the existence preconditions combined with the invariants
        
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