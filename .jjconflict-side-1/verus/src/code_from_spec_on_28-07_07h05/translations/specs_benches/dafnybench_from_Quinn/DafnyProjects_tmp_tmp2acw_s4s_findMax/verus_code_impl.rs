use vstd::prelude::*;

verus! {
    /* 
    * Formal verification of a simple algorithm to find the maximum value in an array.
    * FEUP, MIEIC, MFES, 2020/21.
    * Translated from Dafny to Verus
    */

    // Finds the maximum value in a non-empty array.
    fn findMax(a: &[i32]) -> (max: i32)
        requires a.len() > 0,
        ensures 
            exists|k: int| 0 <= k < a.len() && max == a[k],
            forall|k: int| 0 <= k < a.len() ==> max >= a[k]
    {
        let mut max = a[0];
        let mut i = 1;
        
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                exists|k: int| 0 <= k < i && max == a[k],
                forall|k: int| 0 <= k < i ==> max >= a[k]
            decreases a.len() - i
        {
            if a[i] > max {
                max = a[i];
            }
            i += 1;
        }
        
        max
    }

    // Test cases checked statically.
    fn testFindMax() {
        let a1 = [1, 3, 2];
        let max1 = findMax(&a1);
        assert(max1 == 3);
        
        let a2 = [5];
        let max2 = findMax(&a2);
        assert(max2 == 5);
        
        let a3 = [1, 1, 1];
        let max3 = findMax(&a3);
        assert(max3 == 1);
    }
}

fn main() {}