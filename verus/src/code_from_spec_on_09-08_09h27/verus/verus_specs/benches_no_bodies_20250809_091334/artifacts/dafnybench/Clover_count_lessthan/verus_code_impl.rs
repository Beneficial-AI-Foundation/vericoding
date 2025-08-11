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
        let seq_numbers = numbers.to_seq();
        let mut count = 0i32;
        /* code modified by LLM (iteration 4): changed i to int type to match seq indexing requirements */
        let mut i: int = 0;
        
        /* code modified by LLM (iteration 4): cast seq_numbers.len() to int for comparison */
        while i < seq_numbers.len() as int
            invariant
                0 <= i <= seq_numbers.len(),
                count >= 0,
                count as int == seq_numbers.subrange(0, i).filter(|x: int| x < threshold).len(),
                seq_numbers =~= numbers.to_seq(),
        {
            /* code modified by LLM (iteration 4): use int indexing directly */
            if seq_numbers[i] < threshold {
                count = count + 1;
            }
            i = i + 1;
        }
        
        proof {
            assert(seq_numbers.subrange(0, seq_numbers.len() as int) =~= seq_numbers);
            assert(seq_numbers.to_set() =~= numbers);
            /* code modified by LLM (iteration 4): assert equivalence between filtered sequence and set */
            assert(seq_numbers.filter(|x: int| x < threshold).to_set() =~= numbers.filter(|x: int| x < threshold));
            assert(seq_numbers.filter(|x: int| x < threshold).len() == numbers.filter(|x: int| x < threshold).len());
        }
        
        count
    }
}

fn main() {}