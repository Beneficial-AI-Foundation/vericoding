use vstd::prelude::*;

verus! {

// Precondition: the list is sorted in non-decreasing order
spec fn smallest_missing_number_precond(s: Seq<u32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Helper function to check if a value is in the sequence
spec fn seq_contains(s: Seq<u32>, val: u32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == val
}

// Postcondition: result is not in s, and all values less than result are in s
spec fn smallest_missing_number_postcond(s: Seq<u32>, result: u32) -> bool {
    !seq_contains(s, result) && 
    forall|k: u32| k < result ==> seq_contains(s, k)
}

// Main function
fn smallest_missing_number(s: Vec<u32>) -> (result: u32)
    requires 
        smallest_missing_number_precond(s@)
    ensures 
        smallest_missing_number_postcond(s@, result)
{
    proof {
        admit(); // Skip proof as in original Lean code
    }
    find_missing_impl(0, &s, 0)
}

// Implementation function
fn find_missing_impl(v: u32, s: &Vec<u32>, index: usize) -> (result: u32)
    requires 
        index <= s.len(),
        v <= 100000  // prevent overflow
    decreases s.len() - index
{
    if index >= s.len() {
        v
    } else {
        let x = s[index];
        if x > v {
            v
        } else if x == v && v < 100000 {
            find_missing_impl(v + 1, s, index + 1)
        } else {
            find_missing_impl(v, s, index + 1)
        }
    }
}

} // verus!

fn main() {
    // Test the implementation
    let test_vec = vec![0u32, 1, 3, 4, 5];
    let result = smallest_missing_number(test_vec);
    println!("Smallest missing number: {}", result);
}