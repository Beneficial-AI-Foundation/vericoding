use vstd::prelude::*;

verus! {

// Helper function to check if a sequence is a permutation of another
spec fn is_perm<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}

// Helper function to filter non-zeros from a sequence
spec fn filter_non_zeros(s: Seq<i32>) -> Seq<i32> {
    s.filter(|x: i32| x != 0)
}

// Helper function to filter zeros from a sequence  
spec fn filter_zeros(s: Seq<i32>) -> Seq<i32> {
    s.filter(|x: i32| x == 0)
}

// Helper function to find first index of zero in a sequence
spec fn first_zero_index(s: Seq<i32>) -> int {
    let non_zeros = filter_non_zeros(s);
    non_zeros.len() as int
}

// Precondition for MoveZeroesToEnd
spec fn move_zeros_to_end_precond(arr: Seq<i32>) -> bool {
    true
}

// Postcondition for MoveZeroesToEnd  
spec fn move_zeros_to_end_postcond(arr: Seq<i32>, result: Seq<i32>) -> bool {
    let first_zero_idx = first_zero_index(result);
    &&& is_perm(result, arr)
    &&& result.subrange(0, first_zero_idx) == filter_non_zeros(arr)
    &&& result.subrange(first_zero_idx, result.len() as int) == filter_zeros(arr)
}

// Implementation of MoveZeroesToEnd - simplified to match Lean structure
fn move_zeros_to_end(arr: Vec<i32>) -> (result: Vec<i32>)
    requires move_zeros_to_end_precond(arr@),
    ensures move_zeros_to_end_postcond(arr@, result@),
{
    let mut result = Vec::new();
    let mut zeros_count = 0;
    
    // First pass: collect all non-zero elements
    for i in 0..arr.len()
        invariant 
            result@ == arr@.subrange(0, i as int).filter(|x: i32| x != 0),
            zeros_count == arr@.subrange(0, i as int).filter(|x: i32| x == 0).len(),
    {
        if arr[i] != 0 {
            result.push(arr[i]);
        } else {
            zeros_count += 1;
        }
    }
    
    // Second pass: add all zeros to the end
    for i in 0..zeros_count
        invariant 
            result@.len() == filter_non_zeros(arr@).len() + i,
            result@.subrange(0, filter_non_zeros(arr@).len() as int) == filter_non_zeros(arr@),
            result@.subrange(filter_non_zeros(arr@).len() as int, result@.len() as int) == 
                Seq::new(i as nat, |_j: nat| 0i32),
            zeros_count == filter_zeros(arr@).len(),
    {
        result.push(0);
    }
    
    proof {
        // Prove that result is a permutation of arr
        assert(result@.subrange(0, filter_non_zeros(arr@).len() as int) == filter_non_zeros(arr@));
        assert(result@.subrange(filter_non_zeros(arr@).len() as int, result@.len() as int) == 
               Seq::new(zeros_count as nat, |_j: nat| 0i32));
        assert(zeros_count == filter_zeros(arr@).len());
        
        // The result contains exactly the non-zeros followed by zeros
        let non_zero_part = result@.subrange(0, filter_non_zeros(arr@).len() as int);
        let zero_part = result@.subrange(filter_non_zeros(arr@).len() as int, result@.len() as int);
        
        assert(non_zero_part == filter_non_zeros(arr@));
        assert(zero_part.len() == filter_zeros(arr@).len());
        assert(forall|j: int| 0 <= j < zero_part.len() ==> zero_part[j] == 0);
        
        // This proves the multiset equality
        assert(result@.to_multiset() == arr@.to_multiset());
    }
    
    result
}

fn main() {}

} // verus!