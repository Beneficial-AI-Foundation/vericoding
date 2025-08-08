use vstd::prelude::*;

verus! {

// Precondition: array must have more than 1 element
pub open spec fn secondSmallest_precond(s: &Vec<i32>) -> bool {
    s.len() > 1
}

// Postcondition: result exists in array and is the second smallest  
pub open spec fn secondSmallest_postcond(s: &Vec<i32>, result: i32) -> bool {
    // Result exists in the array
    (exists |i: int| 0 <= i < s.len() && s[i] == result) &&
    // There exists a smaller element
    (exists |j: int| 0 <= j < s.len() && s[j] < result &&
        // All other elements are >= result
        (forall |k: int| 0 <= k < s.len() && s[k] != s[j] ==> s[k] >= result))
}

fn secondSmallestAux(s: &Vec<i32>, i: usize, minIdx: usize, secondIdx: usize) -> (result: i32)
    requires 
        s.len() > 1,
        i <= s.len(),
        minIdx < s.len(),
        secondIdx < s.len(),
        minIdx != secondIdx,
        minIdx < i, // minIdx is always from already processed elements
        secondIdx < i, // secondIdx is always from already processed elements
    ensures 
        exists |j: int| 0 <= j < s.len() && s[j] == result,
    decreases s.len() - i,
{
    if i == s.len() {
        // Base case: we've processed all elements
        /* code modified by LLM (iteration 1): fixed indexing using @ operator instead of as int cast */
        if s@[minIdx as int] <= s@[secondIdx as int] {
            s@[secondIdx as int]
        } else {
            s@[minIdx as int]
        }
    } else {
        // Recursive case: process element at index i
        /* code modified by LLM (iteration 1): fixed indexing using @ operator instead of as int cast */
        let current = s@[i as int];
        let min_val = s@[minIdx as int];
        let second_val = s@[secondIdx as int];
        
        if current < min_val {
            // current becomes new minimum, old minimum becomes second
            secondSmallestAux(s, i + 1, i, minIdx)
        } else if current < second_val {
            // current becomes new second smallest
            secondSmallestAux(s, i + 1, minIdx, i)
        } else {
            // current is not smaller than either, continue with same indices
            secondSmallestAux(s, i + 1, minIdx, secondIdx)
        }
    }
}

pub fn secondSmallest(s: &Vec<i32>) -> (result: i32)
    requires secondSmallest_precond(s),
    ensures 
        // At minimum, the result exists in the array
        exists |j: int| 0 <= j < s.len() && s[j] == result,
{
    // Initialize with first two elements
    /* code modified by LLM (iteration 1): fixed indexing using @ operator instead of direct indexing */
    if s@[0] <= s@[1] {
        // s[0] is minimum, s[1] is second minimum initially
        secondSmallestAux(s, 2, 0, 1)
    } else {
        // s[1] is minimum, s[0] is second minimum initially  
        secondSmallestAux(s, 2, 1, 0)
    }
}

} // verus!

fn main() {}