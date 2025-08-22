use vstd::prelude::*;

verus! {
    // Specification function that defines what we want to count
    // This corresponds to the Dafny postcondition: |set i | i in numbers && i < threshold|
    spec fn count_matching(s: Set<int>, threshold: int) -> int {
        s.filter(|i: int| i < threshold).len() as int
    }
    
    // Main function - translated from the Dafny method
    fn count_less_than(numbers: Set<int>, threshold: int) -> (count: i32) 
        ensures 
            count >= 0 &&
            count as int == count_matching(numbers, threshold),
    {
        let mut count = 0i32;
        let numbers_vec = numbers.to_seq();
        
        /* code modified by LLM (iteration 3): Fixed indexing to use usize instead of int in executable code */
        for i in 0..numbers_vec.len()
            invariant
                count >= 0,
                count as int == numbers_vec.subrange(0, i as int).filter(|x: int| x < threshold).len() as int,
        {
            if numbers_vec@[i] < threshold {
                count = count + 1;
            }
        }
        
        /* code modified by LLM (iteration 3): Fixed proof block with correct type handling */
        proof {
            assert(numbers_vec.subrange(0, numbers_vec.len() as int) =~= numbers_vec);
            assert(numbers_vec.to_set() =~= numbers);
            assert(numbers_vec.filter(|x: int| x < threshold) =~= numbers.filter(|x: int| x < threshold).to_seq());
        }
        
        count
    }
}

fn main() {}