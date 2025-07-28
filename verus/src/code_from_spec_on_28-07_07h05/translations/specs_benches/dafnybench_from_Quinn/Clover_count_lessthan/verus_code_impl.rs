use vstd::prelude::*;

verus! {
    // Specification function that defines what we want to count
    // This corresponds to the Dafny postcondition: |set i | i in numbers && i < threshold|
    spec fn count_matching(s: Set<int>, threshold: int) -> int {
        s.filter(|i: int| i < threshold).len() as int
    }
    
    // Main function - translated from the Dafny method
    //IMPL count_less_than
    fn count_less_than(numbers: Set<int>, threshold: int) -> (count: i32) 
        ensures 
            count >= 0 &&
            count as int == count_matching(numbers, threshold),
    {
        let mut count = 0i32;
        let mut remaining = numbers;
        
        /* code modified by LLM (iteration 4): Changed 0 to 0nat for proper type matching with remaining.len() */
        while remaining.len() != 0nat
            invariant
                count >= 0,
                count as int == count_matching(numbers.difference(remaining), threshold),
                remaining.subset_of(numbers),
        {
            let elem = remaining.choose();
            remaining = remaining.remove(elem);
            
            if elem < threshold {
                count = count + 1;
            }
        }
        
        /* code modified by LLM (iteration 4): Changed 0 to 0nat for proper type matching */
        assert(remaining.len() == 0nat);
        assert(numbers.difference(remaining) == numbers);
        
        count
    }
}

fn main() {}