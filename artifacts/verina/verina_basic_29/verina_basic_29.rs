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
    while i < k
        invariant
            0 <= i <= k,
            k < s.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result[j] == s[j],
        decreases k - i,
    {
        result.push(s[i]);
        i += 1;
    }
    
    // Copy elements after index k, skipping the element at k
    let mut i = k + 1;
    while i < s.len()
        invariant
            k + 1 <= i <= s.len(),
            k < s.len(),
            result.len() == k + (i - (k + 1)),
            forall |j: int| 0 <= j < k ==> result[j] == s[j],
            forall |j: int| k <= j < result.len() ==> result[j] == s[j + 1],
        decreases s.len() - i,
    {
        result.push(s[i]);
        i += 1;
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
    let s = vec![1, 2, 3, 4, 5];
    let k = 2;
    
    if k < s.len() {
        let result = remove_element(&s, k);
        assert(result.len() == 4);
        assert(result[0] == 1);
        assert(result[1] == 2);
        assert(result[2] == 4);  // s[3]
        assert(result[3] == 5);  // s[4]
    }
}

} // verus!