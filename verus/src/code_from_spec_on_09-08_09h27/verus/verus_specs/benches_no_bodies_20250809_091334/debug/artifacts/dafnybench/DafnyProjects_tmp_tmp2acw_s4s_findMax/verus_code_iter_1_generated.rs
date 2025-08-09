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
        
        while i < a.len()
            invariant 
                0 <= i <= a.len(),
                exists|k: int| 0 <= k < i && max == a[k],
                forall|k: int| 0 <= k < i ==> max >= a[k]
        {
            if a[i] > max {
                max = a[i];
            }
            i = i + 1;
        }
        
        max
    }

    // Test cases checked statically.
    fn testFindMax() {
        let arr1 = [1, 3, 2, 5, 4];
        let max1 = findMax(&arr1);
        assert(max1 == 5);
        
        let arr2 = [10];
        let max2 = findMax(&arr2);
        assert(max2 == 10);
        
        let arr3 = [7, 2, 9, 1, 6];
        let max3 = findMax(&arr3);
        assert(max3 == 9);
    }
}

fn main() {}