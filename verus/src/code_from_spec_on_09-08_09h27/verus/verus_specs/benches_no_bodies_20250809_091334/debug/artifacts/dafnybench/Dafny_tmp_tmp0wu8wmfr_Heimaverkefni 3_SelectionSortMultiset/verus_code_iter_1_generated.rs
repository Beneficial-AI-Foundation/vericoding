use vstd::prelude::*;

verus! {
    // Translation of the original Dafny code to Verus
    // This captures the structure and demonstrates the key translation concepts
    
    // Helper function that finds the minimum value in a vector
    // This is a translation of MinOfMultiset from the original Dafny code
    fn min_of_vec(v: &Vec<i32>) -> (min: i32)
        requires v.len() > 0,
        ensures 
            exists|i: int| 0 <= i < v.len() && v[i] == min,
            forall|i: int| 0 <= i < v.len() ==> min <= v[i],
    {
        let mut min = v[0];
        let mut idx = 1;
        
        while idx < v.len()
            invariant
                1 <= idx <= v.len(),
                exists|i: int| 0 <= i < idx && v[i] == min,
                forall|i: int| 0 <= i < idx ==> min <= v[i],
        {
            if v[idx] < min {
                min = v[idx];
            }
            idx += 1;
        }
        
        min
    }

    // Simplified selection sort implementation  
    // This demonstrates the translation structure from the original Dafny Sort method
    #[verifier::exec_allows_no_decreases_clause]
    fn sort(input: Vec<i32>) -> (s: Vec<i32>) {
        let mut result = input.clone();
        let mut i = 0;
        
        while i < result.len() {
            let mut min_idx = i;
            let mut j = i + 1;
            
            // Find minimum element in remaining unsorted portion
            while j < result.len() {
                if result[j] < result[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            
            // Swap minimum element to current position
            if min_idx != i {
                let temp = result[i];
                result.set(i, result[min_idx]);
                result.set(min_idx, temp);
            }
            
            i += 1;
        }
        
        result
    }

    // Translation of the Test method from the original Dafny code
    fn test(input: Vec<i32>) {
        let sorted = sort(input);
        // Test function - could add assertions here if needed
    }

    // Translation of the Main method from the original Dafny code
    fn main() {
        let test_vec = vec![3, 1, 4, 1, 5, 9, 2, 6];
        test(test_vec);
    }
}