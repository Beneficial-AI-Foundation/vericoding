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

    // Count occurrences of each element and find the one with maximum count
    let mut max_count: usize = 0;
    let mut majority_candidate: i32 = -1;
    
    let mut i = 0;
    while i < lst.len()
        invariant 
            0 <= i <= lst.len(),
            max_count <= i,
            majority_candidate == -1 || lst@.contains(majority_candidate),
    {
        let current_element = lst[i];
        let mut count = 0;
        let mut j = 0;
        
        // Count occurrences of current_element
        while j < lst.len()
            invariant
                0 <= j <= lst.len(),
                count == count_occurrences(current_element, lst@.subrange(0, j as int)),
        {
            if lst[j] == current_element {
                count = count + 1;
            }
            j = j + 1;
        }
        
        // Update majority candidate if this element has more occurrences
        if count > max_count {
            max_count = count;
            majority_candidate = current_element;
        }
        
        i = i + 1;
    }
    
    // Check if the candidate is actually a majority element
    if max_count > lst.len() / 2 {
        majority_candidate
    } else {
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