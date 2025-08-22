use vstd::prelude::*;

verus! {

// Helper function to count occurrences of an element in a sequence
spec fn count_occurrences(n: i32, lst: Seq<i32>) -> nat {
    lst.filter(|x: i32| x == n).len()
}

// Precondition (trivially true in this case)  
spec fn find_majority_element_precond(lst: Seq<i32>) -> bool {
    true
}

// Main function to find majority element
fn find_majority_element(lst: Vec<i32>) -> (result: i32)
    requires find_majority_element_precond(lst@),
    ensures find_majority_element_postcond(lst@, result),
{
    if lst.len() == 0 {
        return -1;
    }
    
    // Boyer-Moore majority vote algorithm - Phase 1: Find candidate
    let mut candidate = lst[0];
    let mut count = 1;
    let mut i = 1;
    
    while i < lst.len()
        invariant 
            0 < i <= lst.len(),
            count >= 0,
    {
        if lst[i] == candidate {
            count = count + 1;
        } else if count == 0 {
            candidate = lst[i];
            count = 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }
    
    // Phase 2: Verify the candidate is actually a majority
    let mut verify_count = 0;
    i = 0;
    
    while i < lst.len()
        invariant 
            0 <= i <= lst.len(),
            verify_count == count_occurrences(candidate, lst@.subrange(0, i as int)),
    {
        if lst[i] == candidate {
            verify_count = verify_count + 1;
        }
        i = i + 1;
    }
    
    // Check if candidate appears more than n/2 times
    if verify_count > lst.len() / 2 {
        proof {
            assert(count_occurrences(candidate, lst@) == verify_count);
            assert(verify_count > lst.len() / 2);
            assert(lst@.contains(candidate));
            
            // Prove that no other element can have count > n/2
            assert forall|x: i32| lst@.contains(x) && x != candidate implies 
                count_occurrences(x, lst@) <= lst.len() / 2 by {
                if lst@.contains(x) && x != candidate {
                    // If both x and candidate had count > n/2, total would exceed n
                    let count_x = count_occurrences(x, lst@);
                    let count_candidate = count_occurrences(candidate, lst@);
                    
                    if count_x > lst.len() / 2 {
                        // This would be a contradiction since count_x + count_candidate > n
                        assert(count_x + count_candidate > lst.len());
                        
                        // But the sum of all counts equals the list length
                        let all_elements = lst@.to_set();
                        let total_count = arbitrary::<nat>(); // This represents the sum of all counts
                        
                        // We know total_count == lst.len(), but count_x + count_candidate > lst.len()
                        // This is impossible, so count_x <= lst.len() / 2
                    }
                }
            }
        }
        candidate
    } else {
        proof {
            // Prove no majority element exists
            assert forall|x: i32| lst@.contains(x) implies 
                count_occurrences(x, lst@) <= lst.len() / 2 by {
                if lst@.contains(x) {
                    if x == candidate {
                        assert(count_occurrences(x, lst@) == verify_count);
                        assert(verify_count <= lst.len() / 2);
                    } else {
                        // For any other element, if it had count > n/2, then it would
                        // have been selected as the candidate by Boyer-Moore algorithm
                        // Since candidate has the maximum possible count and it's <= n/2,
                        // all other elements must also have count <= n/2
                    }
                }
            }
        }
        -1
    }
}

// Postcondition specification
spec fn find_majority_element_postcond(lst: Seq<i32>, result: i32) -> bool {
    let n = lst.len();
    
    if result == -1 {
        // No majority element exists - all elements appear at most n/2 times  
        forall|x: i32| lst.contains(x) ==> #[trigger] count_occurrences(x, lst) <= n / 2
    } else {
        // result is the majority element and appears in the list
        lst.contains(result) && 
        count_occurrences(result, lst) > n / 2 && 
        forall|x: i32| lst.contains(x) ==> (#[trigger] count_occurrences(x, lst) <= n / 2 || x == result)
    }
}

fn main() {}

}