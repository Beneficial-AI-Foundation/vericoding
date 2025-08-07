use vstd::prelude::*;

verus! {

// Precondition: k must be within bounds of the array
spec fn remove_element_precond(s: Seq<i32>, k: nat) -> bool {
    k < s.len()
}

// Function to remove element at index k
fn remove_element(s: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k < s.len(),
    ensures
        result.len() == s.len() - 1,
        forall |i: int| 0 <= i < k ==> result[i] == s[i],
        forall |i: int| k <= i < result.len() ==> result[i] == s[i + 1],
{
    let mut result = Vec::new();
    
    // Copy elements before index k
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < k
        invariant
            i <= k,
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result[j] == s[j],
        decreases k - i,
    {
        result.push(s[i]);
        i += 1;
    }
    
    // Copy elements after index k (skipping element at k)
    let mut j = k + 1;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while j < s.len()
        invariant
            k + 1 <= j <= s.len(),
            result.len() == k + (j - k - 1),
            forall |idx: int| 0 <= idx < k ==> result[idx] == s[idx],
            forall |idx: int| k <= idx < result.len() ==> result[idx] == s[idx + 1],
        decreases s.len() - j,
    {
        result.push(s[j]);
        j += 1;
    }
    
    result
}

// Postcondition specification
spec fn remove_element_postcond(s: Seq<i32>, k: nat, result: Seq<i32>) -> bool {
    &&& result.len() == s.len() - 1
    &&& (forall |i: int| 0 <= i < k ==> result[i] == s[i])
    &&& (forall |i: int| k <= i < result.len() ==> result[i] == s[i + 1])
}

// Test function to demonstrate usage
fn main() {
    /* code modified by LLM (iteration 1): removed println! macro calls which are not supported in Verus */
    let v = vec![1, 2, 3, 4, 5];
    let result = remove_element(&v, 2);
    // Note: println! is not supported in Verus verification
    // Original code would print: "Original: [1, 2, 3, 4, 5]"
    // Original code would print: "After removing element at index 2: [1, 2, 4, 5]"
}

} // verus!