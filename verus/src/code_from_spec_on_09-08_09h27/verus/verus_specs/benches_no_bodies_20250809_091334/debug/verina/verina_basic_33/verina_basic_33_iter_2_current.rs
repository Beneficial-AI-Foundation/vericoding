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
    let mut candidate: u32 = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
    while i < s.len()
        invariant
            i <= s.len(),
            candidate <= 100000,
            forall|k: u32| k < candidate ==> seq_contains(s@, k),
            smallest_missing_number_precond(s@)
        decreases s.len() - i
    {
        /* code modified by LLM (iteration 1): added proof block to help verification */
        proof {
            // Help the verifier understand that the current element exists in the sequence
            assert(seq_contains(s@, s[i]));
        }
        
        if s[i] == candidate {
            candidate = candidate + 1;
        } else if s[i] > candidate {
            break;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 1): added proof block to establish postcondition */
    proof {
        // Prove that candidate is not in s
        if seq_contains(s@, candidate) {
            // If candidate were in s, we would have found it during the loop
            let witness_idx = choose|idx: int| 0 <= idx < s@.len() && s@[idx] == candidate;
            assert(false); // This leads to contradiction given our loop invariant
        }
        // The invariant already ensures all k < candidate are in s
    }
    
    candidate
}

// Implementation function
fn find_missing_impl(v: u32, s: &Vec<u32>, index: usize) -> (result: u32)
    requires 
        index <= s.len(),
        v <= 100000  // prevent overflow
    decreases s.len() - index
{
    if index >= s.len() {
        return v;
    }
    
    if s[index] == v {
        find_missing_impl(v + 1, s, index + 1)
    } else if s[index] > v {
        v
    } else {
        find_missing_impl(v, s, index + 1)
    }
}

} // verus!

fn main() {
}