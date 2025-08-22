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
    if s.filter(|x: i32| x == 0).len() == 0 {
        s.len() as int
    } else {
        let mut i = 0;
        while i < s.len() && s[i] != 0 {
            i = i + 1;
        }
        i
    }
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
    let mut zero_count = 0;
    
    // First pass: collect all non-zero elements
    for i in 0..arr.len()
        invariant
            result.len() + zero_count == i,
            result@ == arr@.subrange(0, i as int).filter(|x: i32| x != 0),
            zero_count == arr@.subrange(0, i as int).filter(|x: i32| x == 0).len(),
    {
        if arr[i] != 0 {
            result.push(arr[i]);
        } else {
            zero_count += 1;
        }
    }
    
    // Second pass: add all zeros at the end
    for i in 0..zero_count
        invariant
            result.len() == arr@.filter(|x: i32| x != 0).len() + i,
            result@.subrange(0, arr@.filter(|x: i32| x != 0).len() as int) == arr@.filter(|x: i32| x != 0),
            result@.subrange(arr@.filter(|x: i32| x != 0).len() as int, result.len() as int) == 
                Seq::new(i as nat, |_j: nat| 0i32),
    {
        result.push(0);
    }
    
    proof {
        assert(result@ == filter_non_zeros(arr@) + filter_zeros(arr@));
        assert(is_perm(result@, arr@)) by {
            assert(result@.to_multiset() == (filter_non_zeros(arr@) + filter_zeros(arr@)).to_multiset());
            assert((filter_non_zeros(arr@) + filter_zeros(arr@)).to_multiset() == 
                   filter_non_zeros(arr@).to_multiset().add(filter_zeros(arr@).to_multiset()));
            assert(arr@.to_multiset() == 
                   arr@.filter(|x: i32| x != 0).to_multiset().add(arr@.filter(|x: i32| x == 0).to_multiset()));
        }
        
        let first_zero_idx = first_zero_index(result@);
        assert(first_zero_idx == filter_non_zeros(arr@).len() as int);
        assert(result@.subrange(0, first_zero_idx) == filter_non_zeros(arr@));
        assert(result@.subrange(first_zero_idx, result@.len() as int) == filter_zeros(arr@));
    }
    
    result
}

fn main() {}

} // verus!