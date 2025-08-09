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
        return s[secondIdx];
    }
    
    let current = s[i];
    let min_val = s[minIdx];
    let second_val = s[secondIdx];
    
    if current < min_val {
        // New minimum found, old minimum becomes second
        secondSmallestAux(s, i + 1, i, minIdx)
    } else if current < second_val && current != min_val {
        // New second minimum found
        secondSmallestAux(s, i + 1, minIdx, i)
    } else {
        // No change
        secondSmallestAux(s, i + 1, minIdx, secondIdx)
    }
}

pub fn secondSmallest(s: &Vec<i32>) -> (result: i32)
    requires secondSmallest_precond(s),
    ensures 
        // At minimum, the result exists in the array
        exists |j: int| 0 <= j < s.len() && s[j] == result,
{
    // Initialize with first two elements
    let (minIdx, secondIdx) = if s[0] <= s[1] {
        (0, 1)
    } else {
        (1, 0)
    };
    
    secondSmallestAux(s, 2, minIdx, secondIdx)
}

} // verus!

fn main() {}