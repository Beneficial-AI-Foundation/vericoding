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
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Test cases checked statically.
    fn testFindMax() {
    // TODO: Remove this comment and implement the function body
    }
}

fn main() {}